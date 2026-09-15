# PLAN — composition in the EXECUTOR, not at the contract level

**Status:** design note. Nothing built. Written 2026-09-15 after a day of
work on contract-level composition made the alternative visible.

---

## §0. The claim

> Composition belongs in the symbolic executor. At a block boundary the
> executor should **consume** the block's precondition and **produce** its
> postcondition, skipping the instructions — exactly as it already does at a
> function call. Loops are the same move with an invariant.

The consequence is that a cut program stays **one** `gen_contract` with **one**
instruction table and **one** end theorem, and the entire Iris-level
composition layer stops being necessary.

---

## §1. The mechanism already exists

`theories/Symbolic/Monads.v:1377`:

```coq
Definition call_contract {Δ τ} (c : SepContract Δ τ) : ⊢ SStore Δ -> SHeapSpec (STerm τ) :=
  fun w0 args =>
    match c with
    | MkSepContract _ _ Σe δe req result ens =>
        evars <- angelic_ctx id Σe ;;                    (* instantiate logic vars *)
        _     <- assert_eq_nenv (subst δe evars) args ;; (* match arguments        *)
        _     <- consume req evars2 ;;                   (* CONSUME precondition   *)
        res   <- demonic (Some result) τ ;;
        _     <- produce ens … ;;                        (* PRODUCE postcondition  *)
        pure res
    end.
```

This is the proposal, already written, already sound:

| piece | where |
|---|---|
| symbolic | `Symbolic/Monads.v:1377` |
| refinement | `Symbolic/Monads.v:1567`, `cext_call_contract` |
| shallow | `MicroSail/ShallowExecutor.v:440,466` |
| soundness | `MicroSail/ShallowSoundness.v:71` |
| in use | `MicroSail/SymbolicExecutor.v:720` (foreign calls) |

Nothing about it is specific to *functions*; it is specific to *having a
contract*. What is missing is a caller for it at CFG-block granularity.

---

## §2. Why this dissolves the frictions rather than solving them

Every obstacle hit on 2026-09-15 is an artifact of composing **after** the
executor has finished, rather than **inside** it.

| observed friction | cause | under executor composition |
|---|---|---|
| per-segment sub-table, `itable_faith_of_segment`, `seg_instr_table_ok` | each segment carries its own table | gone — the table stays the whole program's |
| `cfg_instrs_verified_composed` + an unsupplied `ImplPre` (`Example/ZZPhase5.v:71`) | a composed chain is not a contract, so it needs its own bridge | gone — the program is still one contract |
| `noninterferent_strong` cannot express entry partway into a program (it ties `read_register pc = bv.of_N init_addr` to `mem_has_instrs μ (bv.of_N init_addr)`) | the trusted statement assumes execution starts at the code base | gone — entry is still the program's base |
| `GenCompose.v`'s 38 lemmas; `seg_run`/`seg_then`/`loop_runs` | reassembling by hand what the executor took apart | mostly superseded |
| `tailChain` destructing 22 conjuncts to re-frame them | the executor's heap is gone by then | gone — the heap is never disassembled |
| `seg_addr (ia+1056) 52` vs `bv.of_N (ia+1108)`; `of_N (a+b)` vs `of_N a + of_N b` | hand-written hand-offs match syntactically | far fewer such seams |

**The diagnosis in one line:** `seg_run` / `seg_then` / `loop_runs` exist to
reassemble state that the executor would never have taken apart.

### What the measurements already said

Two matched comparisons from the same day, both real:

| | data | proof |
|---|---|---|
| segment G, hand-written (`ZZMladDvLoop.v`) | 130 | 167 |
| segment G, on `GenCompose` (`ZZMladDvLoop2.v`) | 71 | 76 |
| tail chain, raw bridge ×5 (`ZZMladTail.v`) | 215 | 334 |
| tail chain, ported (`ZZTailPorted` + `ZZSpikeEnter2`) | 140 | 157 |

Composition-as-lemma-application is ~2× better than hand-rolling it. But both
columns are **cost that executor-level composition does not incur at all** —
the right comparison is not 334 vs 157, it is 157 vs a table entry.

---

## §3. What survives, and what does not

**Survives — and it is the bulk of the recent work:**

- the block **contracts** themselves: footprints (§R14), self-containment and
  `PVVar` (§R17), the publicness weakenings (§R18). These *become* the block
  contracts.
- `gen_seg_contract` and `LoopSpec` as the way to *write* them.
- `GenContract.v`, the executor, the solver, `Adequacy`, `EndToEnd` — untouched.
- every diagnostic record.

**Superseded:**

- `GenCompose.v`'s composition half — `seg_run`, `seg_run_single_exit`,
  `seg_run_pinned_exit`, `seg_then`, `seg_then_loop`, `seg_loop`, `loop_runs`,
  `loop_by_induction`, `loop_enter_from_seg`, `loop_entry_by_subst` and the
  frame-transfer family.
- the chains built on them: `ZZMladTail.v`, `ZZTailPorted.v`, and
  `ZZSpikeEnter2.v`'s composition half.
- `cfg_instrs_verified_composed` and the `ImplPre`-for-composed-chains problem.

**Note against self-interest:** `ZZTailPorted.v` was written the same afternoon
and would be discarded. Its lasting value is the measurement in §2, which is
what made the comparison concrete.

**Retained from `GenCompose` regardless:** the `loop_carry` / `loop_cells_trade`
reservoir machinery is about what a loop OWNS across trips, which any loop rule
needs — see §5.

---

## §4. The design

### 4.1 A block-contract table

The CFG analogue of `CEnv`: a map from an entry address term to a contract
plus its declared exits.

```
BlockTable ≈ list (entry : STerm ty_xlenbits,
                   pre  : Assertion Σ,
                   post : Assertion (Σ ▻ "an"),
                   exits : list (STerm ty_xlenbits))
```

`gen_seg_contract` already produces exactly these fields; a `CFGVerifierContract`
is one entry minus its `cfg_instrs`/`cfg_placement`, which the block form does
not need since the instructions are not re-tabled.

### 4.2 The hook

`Verifier.v:986`, `sexec_cfg_addr`. Current dispatch, after the exit check:

```coq
if andb (negb first) (is_exit exits apc) then pure apc else
  (match lookup_instr tbl apc with
   | None         => emsg "…no instruction key matches this pc term"
   | Some (wd, ai) => … chunk_gc … execute …)
```

The change is one branch **before** `lookup_instr`:

```coq
match lookup_block btbl apc with
| Some blk => consume (pre blk) ;; demonic over (exits blk) ;;
              produce (post blk) ;; continue at the chosen exit
| None     => (existing instruction path)
end
```

Consuming the precondition is what forces the caller to actually own what the
block needs — the executor's existing `consume` already reports a residual when
it does not.

### 4.3 The VC obligation per block

Each block contract is discharged exactly as today: `ValidCFGVerifierContract`
over its own instructions. That part is unchanged and is where all of §3's
surviving work lives. What changes is only that the *caller* no longer re-runs
the instructions.

---

## §5. The loop rule — the genuinely new part

A function call never returns to its own entry; a loop does, so `call_contract`
alone is not the rule. The shape to aim for, at a loop head:

1. **consume** the invariant at the head;
2. **havoc** what the loop modifies (the executor already has `demonic`);
3. **produce** the invariant plus the exit guard at the exit address;

with a separate obligation, discharged as its own VC, that the body preserves
the invariant — which is what `LoopSpec`'s `loop_body_contract` already is.

Two things carry over unchanged from the current work and should not be
re-derived:

- **`loop_carry` / `loop_cells_trade`** (§R6): what a sliding-footprint loop
  owns across trips, and the observation that the trade is a pure permutation.
  Any loop rule needs this.
- **the trip valuation** `iota` and the disjointness criterion — two cells
  sharing a base whose offsets differ by a multiple of the walk step overlap
  across trips, which makes a reservoir vacuous (§R11, segment D).

**Open:** whether the invariant is consumed/produced at the head (a rule), or
the loop keeps an induction that the executor calls into. The first is cleaner;
the second is closer to what is proved today.

---

## §6. Risks and open questions

1. **Soundness is analogous, not identical.** A function call returns to its
   caller; a block "returns" by setting the pc to a declared exit, and several
   exits mean a demonic choice. The `contractsSound` analogue must relate that
   to the block's own VC. **This is the item to settle before building
   anything.**
2. **Fuel accounting changes** — a block costs one step rather than its
   instruction count. Every existing fuel figure becomes wrong in the safe
   direction, but `is_exit`'s interaction with fuel was already subtle
   (`Verifier.v`'s `first` flag, and `diagnostics/table-entry-cost.md` §3's exit
   overshoot).
3. **The `first` flag.** It exists because a loop-body contract starts and ends
   at the same address, so the pc cannot distinguish the two visits. Under
   executor composition the loop head is a *block boundary*, so this may change
   shape — or may need the same trick. Do not assume it disappears.
4. **Does a block contract need `assert_eq_nenv`?** `call_contract` matches the
   callee's parameters against the caller's arguments. A block has no argument
   list — its "arguments" are the machine state, which the precondition already
   describes. Probably the step is simply absent, but that is exactly the kind
   of "probably" that costs a day.
5. **Cost is unmeasured and could go either way.** Replacing N instructions by
   one consume+produce should be cheaper, but `consume` on a large precondition
   is not free, and `diagnostics/lvar-lookup-cost-drivers.md` says a declared
   existential is expensive. **No claim of a speedup until a matched pair is
   measured.**

---

## §7. Proposed spike, smallest first

**Do not start with loops.** Order:

1. **Straight-line, one block.** A two-segment program; verify it flat, then
   verify it with the first segment replaced by its contract. Same end theorem
   both ways. This settles §6.1 and §6.4 and gives the first cost pair.
2. **Straight-line, chained.** Three blocks, to check that a produced
   postcondition is consumable as the next block's precondition without
   hand-written glue — the property `tailChain` spends 90 lines on.
3. **A counted loop**, on the §5 rule, against `PaddedLoop.v` or
   `Countdown`, both of which are gate-checked and small.
4. **Only then** muladd, where the contracts already exist.

Each step's acceptance test is the same and is already standard here: the end
theorem is `noninterferent_strong` for the whole program, and a falsification
arm is REJECTED (a deliberately-wrong exit or a wrong pinned value).

---

## §8. What this means for the muladd work

Segments A/BC/D/E/F/G/H/I/J/K/L/M/N and their contracts stay. The loops' specs
stay. The framing, self-containment and publicness work stays. What stops being
needed is the assembly — and with it the reason muladd has no end theorem
today: there is no whole-program chain, and building one at the contract level
was going to require either restating the tail as a standalone program or
generalising `noninterferent_strong`'s entry address.

Under this design neither is needed: muladd stays one program with one
`gen_contract`, its thirteen blocks are replaced by their contracts, and the end
theorem is the three-line route that `muladd_q_noninterferent_param` already
takes.
