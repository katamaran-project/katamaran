# PLAN: replace exit conditions by ONE exit address

Status: DRAFT 2026-09-25, rev 2. Nothing implemented. Origin: the TODOS.txt
PRIORITY item (Emiel, 2026-09-25). Goes BEFORE PLAN-valid-blk-annot.md (§7).

## 0. Decisions (Emiel)

- A contract has exactly ONE exit, and its run stops exactly when `pc = exit`.
  No predicates, no sets.
- Each example's exit pc is known, so the trusted statement names it directly
  (`init_addr + k`). There is no generic "the pc left the code" condition.

## 1. What is deleted

| today | fate |
|---|---|
| `cfg_exitCond : bv -> bool` (contract field) | deleted |
| `cfg_exits : list (Term Σ ty_xlenbits)` | becomes `cfg_exit : Term Σ ty_xlenbits` |
| `SExitTable`, `exits_of_offs`, `persist_etable`, list-`is_exit` | one term; `is_exit` = `Term_eqb (peval apc) exit` |
| `etable_rel`, `etable_relW` (VerifierRel.v, 58 uses in 12 files) | deleted, since there is only one representation of the exit |
| `HexitsFaith` (EndToEnd.v, 13 uses), `HexitOffs` | deleted |
| `extra_exit_offs` (gen_contract_*) | becomes `exit_off : N` |
| `seg_exitCond`, `seg_exitCond_inv1`, `seg_exit_table_ok`, `etable_faith_exits_of_*` | deleted |
| `pcOutOfInstrs_exitCond`, `pcOutOfInstrs_fallthrough` (Noninterference.v) | deleted |
| local `head_/tail_/cut_/countdown_/jmp_fwd_/KSL _exitCond` in Result files | deleted |
| `blk_off` (BlkAnnot) and `Hexit` in `blockSound_of_contract` | deleted: a block resumes at its contract's exit (§3d) |

Generic layers that STAY untouched: `theories/SmallStep/Step.v`
`StepsWithExitCond`, `theories/Iris/BinaryAdequacy.v`
`adequacy_gen_withExitCond`, and `Noninterference.v`'s
`RiscVStepsWithExitCond` (all take an arbitrary predicate). They get
instantiated with `fun pc => pc = exit`.

## 2. The trusted statement

```coq
Definition noninterferent_strong
    (init_addr : N) (instrs : list AST)
    (exit_addr : N)                     (* was: exitCond : bv xlenbits -> bool *)
    (reg_specs : list reg_spec) (mem_specs : list mem_full_spec) : Prop :=
  ∀ …,  (* premises unchanged *)
    ∀ n γ1' μ1',
      ⟨ γ1, μ1 ⟩ -(atPc exit_addr, n)->* ⟨ γ1', μ1' ⟩ →
      ∃ γ2' μ2', ⟨ γ2, μ2 ⟩ -(atPc exit_addr, n)->* ⟨ γ2', μ2' ⟩ ∧ leakage_trace μ1' = leakage_trace μ2'.

Definition atPc (a : N) : Val ty_xlenbits -> Prop := fun pc => pc = bv.of_N a.
```

`atPc` is the one new trusted definition, and it is a single equation.

**Meaning change, for review.** Today 14/17 theorems quantify over runs that
stop when `pc ≥ ia + 4|code|`. After this change they quantify over runs that
stop when `pc = exit`. These are different run relations. A run that leaves the
code at some other address is no longer a stopping run, and it keeps going,
so the theorem says nothing about it. Our VCs already prove that every path
reaches exactly the declared exit term (the executor can only stop on one), so
no VC should get harder. That is a prediction, not a measurement.

## 3. Design of the CFGVer side

### 3a. Contract

```coq
Record CFGVerifierContract {Σ} :=
  { cfg_init_addr ; cfg_placement
  ; cfg_exit : Term Σ ty_xlenbits      (* replaces cfg_exits + cfg_exitCond *)
  ; cfg_precondition ; cfg_instrs ; cfg_fuel ; cfg_postcondition }.
```

For a parametric-base contract `cfg_exit = q + exit_off` (`term_var "p"` for
gen_contract_*, the contract's own base for gen_seg_contract). The generators
build it, so authors write only `exit_off`.

### 3b. Executor (Verifier.v)

`sexec_cfg_addr`'s stop test is `if andb (negb first) (Term_eqb (peval apc) exit)`.
That is today's test on a one-element list. `first` stays: it is what lets a
loop body start AND end at the same address (offset 0), see R-B.

### 3c. Soundness (Adequacy.v, VerifierRel.v)

- `cexec_cfg_addr` stops when `v = inst exit ι`. The concrete side does not need
  its unconditional `angelic_binary` any more, but it may keep it (it is the
  sound direction).
- `myWP2_loop`'s `ExitCond := ∃ v, pc ↦ᵣ SyncVal v ∗ ⌜v = inst exit ι⌝`.
- `etable_rel` disappears from `rexec_cfg_addr` and
  `sound_scfg_verification_condition_myWP2`. Its only job was to relate
  `is_exit` to `exitCond`, and `is_exit`'s soundness is now
  `Term_eqb_spec` + `peval_sound`.
- **R-B resolved on paper:** `myWP2_loop_fix` is `ExitCond ∨ step`, a
  DISJUNCTION the prover chooses at every unfolding. So a body contract whose
  exit equals its start is no problem at the Iris level: at step 0 we take the
  step branch. Only the TOP-LEVEL run relation tests the exit before step 0, and
  there `exit ≠ init_addr` for every example (§4). Needs no new machinery.

### 3d. Blocks

A block resumes where its contract exits, i.e. at `inst (cfg_exit c) ι`,
with ι the valuation chosen while consuming the precondition.
- `sexec_block` produces the post and returns `persist cfg_exit`, not
  `apc + blk_off`.
- The post already speaks about `"an"`, and "an" := that term.
- `BlkAnnot` becomes `(blk_ctx, blk_contract)`, and PLAN-contract-ast §2b is done.
- `blockSound`'s conclusion reads `pc ↦ᵣ inst (cfg_exit c) ι`.

### 3e. Placement

`cfg_exit` is a term over the symbolic base. The concrete exit address is
`inst cfg_exit ι`, and `seg_pre_placement` / the gen_contract base fact already
give `inst base ι = init_addr`. So the bridges get `inst cfg_exit ι =
bv.of_N (init_addr + exit_off)` by `bv.of_N_add`, once per generator, and
never at a call site.

## 4. Per-example exit pcs

Standalone examples (gen_contract_* bridges; today `extra_exit_offs = []`,
exit table = fall-through only). **The exit is the fall-through
`init_addr + 4·|code|`**:

| Result file | program | exit pc |
|---|---|---|
| SetX2Result | `[ADDI X2 X0 42]` | `init_addr + 4` |
| MvSwapResult | `[MV;MV;MV]` | `init_addr + 12` |
| CountdownResult (`countdown`) | `[ADDI; BNE]` | `init_addr + 8` |
| CountdownResult (`countdown_mem`) | `countdown_mem_instrs` | `init_addr + 4·|countdown_mem_instrs|` |
| JumpsResult (`jmp_fwd`) | `[JAL X0 8; NOP]` | `init_addr + 8` (the JAL target IS the fall-through) |
| Cmovznz4Result | `cmovznz4_instrs` | `init_addr + 4·|…|` |
| PrecomputeResult | `precompute_instrs` | `init_addr + 4·|…|` |
| KeyScheduleLoopResult | `key_schedule_loop2_instrs` | `init_addr + 4·|…|` |
| BearSSLModpowResult | `modpow_win_instrs` | `init_addr + 4·|…|` |
| BearSSLModpowFullResult | `modpow_win_full_instrs` | `init_addr + 4·|…|` |
| BearSSLMuladdResult | `muladd_q_instrs` | `init_addr + 4·|…|` |
| BearSSLCheckScalarResult | `check_scalar_instrs` | `init_addr + 4·|…|` |
| BearSSLCheckScalarLoop1Result | `loop1_instrs` | `init_addr + 4·|…|` |

For the long programs the statement writes the literal: compute
`4·|instrs|` once when porting and write e.g. `(init_addr + 280)%N`. Do not keep
`length instrs` in the statement, because the whole point is that the exit is
readable.

Composed examples (whole program; today `pcOutOfInstrs_exitCond 0 …` at the top
level, target-style internally). Internal segment exits are listed for
the generator port:

| Result file | top-level exit | internal segments (exit_off) |
|---|---|---|
| CountdownRecResult | `init_addr + 12` | loop block `cdRec` 8; link `cdLink` 12 |
| CountdownComposedResult | end of program | `cdBody` 0 (loop body), `cdFinal` 8 |
| PaddedLoopResult | end of program | body 0, final 8 |
| SwapComposedResult | `12` (base 0) | `swapA` 4, `swapB` 12 |
| TwoLoopsComposedResult | end of program | bodies 0, cuts 8 / 16 |

"End of program" = its fall-through. Fill in the literal during the port.

### 4a. The one real problem: `jumpIfZero` has TWO exits

`[BEQ X1 X0 8]`, where `extra_exit_offs = [8]`: fall-through at `+4`, branch at
`+8`. It is the only tracked example with two exits (the multi-exit muladd
probes are untracked ZZ files). Options:
- **(a) Give the two paths a shared exit point:** `[BEQ X1 X0 8; NOP]`, where
  both paths reach `init_addr + 8`. That changes the program in the trusted
  statement, but the example's intent (branch on a public register) is kept.
- **(b) Drop it:** `jmp_fwd`, `countdown` and the BearSSL loops already cover
  branching.

**Decided 2026-09-25 (D4): (a), implemented.** The rationale is the one in §8 D2: real code has one exit per function, and segments are cut at join points.

## 5. Phases

1. **Types + executor** (Verifier.v, Contracts.v): `cfg_exit`, delete
   `cfg_exitCond`/`cfg_exits`/`SExitTable`/`blk_off`; `sexec_cfg_addr` stop
   test; `sexec_block` resumes at the exit. Light examples break (fixed in 3).
2. **Refinement + soundness** (VerifierRel.v, TablesRel.v, Adequacy.v):
   `cexec_cfg_addr`/`cexec_block` mirrors, delete `etable_rel`, `myWP2_loop`
   ExitCond at `pc = exit`. Re-prove `rexec_cfg_addr`, `rexec_block`,
   `sound_scfg_verification_condition_myWP2`, `blockSound_of_vc`,
   `blockSound_of_contract` (loses `Hexit`).
3. **Generators + light examples** (GenContract.v, GenSegment.v, GenCompose.v,
   Example/*.v): `extra_exit_offs`/`targets` become `exit_off`; delete
   `seg_exitCond` & co; each VC re-run unchanged apart from the table shape.
   Apply §4a to Jumps.v.
4. **Trusted statements** (Noninterference.v, EndToEnd.v, Example/*Result.v):
   `atPc`, the new `noninterferent_strong`, drop `HexitsFaith`/`HexitOffs` from
   the bridges, and port the 17 Result files with the §4 literals. **Emiel
   reviews the Noninterference.v + Result.v diff before the gate.**
5. **R-A: drop `cfg_init_addr` and the `ia` contract parameter**, if no bridge
   still reads it. Today `cdRec ia` etc. carry `ia` for `cfg_init_addr` and
   `seg_exitCond ia`. The latter is gone after Phase 3, so check the former.
6. **Cleanup:** the skills (`cfgver-contracts`, `cfgver-executor`,
   `cfgver-gen-contract`, `cfgver-endtoend*`, `cfgver-soundness`,
   `cfgver-new-example`'s "choosing exitCond" step), the TODOS.txt
   PRIORITY item and the `etable_rel` item, and the Verifier.v comments on
   `blk_off` (~line 181).

Run the gate after Phase 4, and again after Phase 5 if done. Per CLAUDE.md, diff
the trusted surface at every phase: phases 1–3 must NOT change it.

## 6. Risks

- **R-A** (Phase 5): whether `cfg_init_addr` can go.
- **R-C**: VC cost. The exit table goes from a list to one term, which should
  be neutral or a small win. Spot-check two examples (Cmovznz4 and CountdownRec)
  with `allocated_words` before and after Phase 3. Do not assume.
- **R-D**: the ZZ muladd probes with two exits (segment L `[56;108]`, segment H
  `[112;228]`) must be split when revived. Untracked, so not gate-blocking.
- **R-E**: `ni_rel_corollary` (Cmovznz4, KSL) and the `_at_start` variants
  instantiate `init_addr` concretely. The exit literal must be instantiated
  consistently, e.g. `cmovznz4_start + k`.

## 7. Why before PLAN-valid-blk-annot.md

After this plan `BlkAnnot` = (ctx, contract), R1/R4 there are moot,
`aiv_loop` is a `bool`, and `blkValid` has no exit side. Valid-blk Phase 1
(span containment in the VC) is independent and may land first.

## 8. Decision log (with revert paths)

Each entry: what was decided, why, and how to undo it. Commits are named by
subject line, since hashes are filled in after the fact.

| # | date | decision | why | revert |
|---|---|---|---|---|
| D1 | 2026-09-25 | Remove `cfg_exitCond`. Exits are addresses, not predicates. | Exit conditions only existed to be related back to the executor's exit terms (etable_rel & co), and forced the `ia` parameter on every contract. | Not implemented yet. Once it is, revert the Phase commits. The generic `StepsWithExitCond` layer is kept, so the old statements can be restored on top of it. |
| D2 | 2026-09-25 | Exactly ONE exit: `pc = exit`, not `pc ∈ exits`. | Whole functions exit through `ret` → one address (`ra`), even with several `ret`s. Multi-exit only arises for intra-function cuts, and those can always be cut at the join point (SESE regions; loops as blocks, cf. CountdownRec). | Weaken to a list later if a real program needs it: `atPc` becomes membership, and `cfg_exit` becomes a list. It is purely additive on top of D1. |
| D3 | 2026-09-25 | Trusted statements write each example's exit as a literal (`init_addr + k`). | Readability: the exit is the one thing a reader must check. | Change `atPc exit` back to a computed `init_addr + 4 * length instrs` in `noninterferent_strong`, which is a mechanical Result-file edit. |
| D4 | 2026-09-25 | `jump_if_zero` becomes `[BEQ X1 X0 8; NOP]` (join point), with exit `+8`. **Implemented** in commit 27a2fd1a ("jump_if_zero: one exit at the join point (NOP)"). | It was the only tracked two-exit example. The NOP is the "cut at the join point" discipline from D2. | `git revert 27a2fd1a`. It touches only Jumps.v, JumpsResult.v, one GenContract.v comment and two skill bodies, so it reverts cleanly as long as nothing later edits those lines. The bridge `gen_contract_noninterferent_param` (non-simple) and `extra_exit_offs` still exist, so the old proof compiles as-is until Phase 3 of this plan deletes them. |
| D5 | 2026-09-25 | Function-level exits (`ret`) are handled by quantifying the exit address with the premise `read_register γ ra = ret_addr`. They are not special-cased in `atPc`. | Keeps `atPc` a single equation. | Nothing to revert yet (no example uses `ret`). |
| D6 | 2026-09-25 | This plan goes BEFORE PLAN-valid-blk-annot.md. | Removes `blk_off`, R1 and R4 there. | Reorder. Valid-blk Phase 1 is independent in either order. |

**Note on D4's trusted-surface change:** `jumpIfZero_noninterferent_param`'s
statement changed. The program gained a NOP, and the bound premise went from
`init_addr + 4 < lenAddr` to `init_addr + 8 < lenAddr`. Checked
axiom-clean (pure_decode, mmioenv) after the change.
