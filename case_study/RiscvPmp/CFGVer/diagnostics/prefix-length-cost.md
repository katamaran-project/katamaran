# Program length is a QUADRATIC cost driver for a symbolic segment contract

Status: **Diagnostic record, 2026-09-04.** Prompted by the question "is having
many instructions around also a performance problem?", asked of the countdown
loop specifically. `composition-payoff.md` §2.1 had answered the prefix-length
question on a *straight-line* 3-instruction segment and found it nearly free
(1.155× over 32 filler instructions). Asked again of the **loop-body segment
contract**, the same axis behaves completely differently.

## One-sentence finding

A segment contract whose branch condition the solver cannot decide by
computation costs **93.81 + 4.05·P + 0.531·P² M words** in the number `P` of
**never-executed** instructions sharing its table — an exact quadratic
(held-out **+0.0024%**) worth **26.9× over 64 filler instructions** — while the
*same* contract with its counter pinned costs 1.42×, the flat unrolled VC of the
same loop 1.60×, and §2.1's straight-line segment 1.35×. So program length is
free for everything except the one construct a loop invariant is made of, where
it is quadratic.

## 0. Protocol

| tag | protocol |
|---|---|
| **ALLOC** | `OCAMLRUNPARAM='v=0x400'`, one heavy proof per `coqc` process, `allocated_words` net of an imports-only baseline re-measured per family, `/usr/bin/time` for peak RSS |

Proof protocol is `vm_compute. solve_vc. Qed.` in every arm — `Qed` throughout.
The unpinned arms carry three residual-closing tactics before `Qed` (priced at
~0.004% by this directory's own rule); the pinned and flat arms close on
`solve_vc` alone, which is the same asymmetry `composition-payoff.md` §4
documents.

Four baselines, one per family: 605,864,905 / 605,871,490 / 605,864,980 /
605,846,159 — a spread of **25,331 words in 6.06e8 (0.0042%)**, which is what
licenses comparing across them.

Three independent reproductions of published figures, on this commit, confirm
the rigs are measuring the same objects as the earlier records:

| arm | here | published | delta |
|---|---|---|---|
| flat unrolled, N=8 | 15.646 | 15.632 | +0.09% |
| flat unrolled, N=16 | 27.868 | 27.862 | +0.02% |
| `ZZCmpBodyPin` (re-run) | 10.660 | 10.66 | 0.00% |
| `ZZU5_K0` / `_K32` | 7.220 / 8.339 | 7.223 / 8.343 | −0.04% |

**A `Prelude.v` rebuild stales `ZZPadCommon.vo`**, and the arms then read as
*cheaper than free* (490.8 M against a 605.9 M baseline) with a bare
`Error: ... makes inconsistent assumptions over library ... Prelude`. Rebuild
`ZZPadCommon.vo` after anything touches `Prelude`. This recurred twice on
2026-09-04, and the plumbing work rebuilds `Prelude` constantly.

**Never measure while anything else rebuilds the shared source tree.** A sweep
run 2026-09-04 while sibling processes rebuilt `Tables.vo`/`TablesRel.vo`
returned `Error:` in all three arms *at identical baseline-level cost* (within
826 words) — the "this variant is free" failure mode, caused by concurrent `.vo`
churn rather than by anything in the arms. Re-run serially, the same arms cost
3.5× more. Parallel workers measuring in one working tree corrupt each other's
numbers silently; only the `Error` gate caught it.

**Gate:** every arm grepped for `Error`. This caught the known stale-`.vo` trap
(`footprint-vs-throughput.md` §5) on the structural-count arms, which would
otherwise have reported as "free".

## 1. Axes

| axis | states | rig |
|---|---|---|
| **prefix length P** | 0 / 16 / 32 / 64 never-executed instructions before the loop | all rigs |
| **proof structure** | composed segment contract vs flat unrolled VC | `ZZPadB*` vs `ZZPadF*` |
| **counter knownness** | symbolic `k` vs `k` pinned to 5 | `ZZPadB*` vs `ZZPadP*` |
| **branch decidability** | undecidable branch vs straight-line | `ZZPadB*` vs `ZZU5_K*` |
| conjunct order (control) | pin before vs after the guard | `ZZPadP0` vs `ZZPadPrev0` |

Held fixed across every `P` within a rig: the executed loop
(`ADDI X1 X1 -1 ; BNE X1 X0 -4`) is byte-identical, the entry pc is set to `4·P`
so **executed steps are identical**, `|Σ|` is identical (1 for the segment rigs,
0 for the flat rig — and `P` mints nothing), the chunk inventory is identical
(X1 only), and the fuel is identical.

**Filler goes BEFORE the loop on purpose.** The loop's fall-through then still
lands exactly one past the end of the table at every `P`, so the exit/infeasible
branch has the same shape in every arm. Padding *after* would put a filler
instruction at the fall-through address and change the branch structure — a
second axis. Filler is `MV X4 X4`, the same filler `ZZU5Common` uses, so these
numbers are comparable in kind to §2.1's.

`drop_fuel` is **0** (`Verifier.v:934`), so `drop_dead` is `pure tt` and
`var_dead`'s O(K) instruction-table scan never runs. **Whatever this record
measures, it is not that scan** — a `drop_fuel > 0` sweep along this axis is a
separate (and probably much worse) story, unmeasured.

## 2. Results

### 2.1 The composed loop-body contract — exactly quadratic in P

| P | net M words | vs P=0 | marginal M/filler instr |
|---|---|---|---|
| 0 | 93.809 | 1.00× | — |
| 16 | 294.473 | 3.14× | 12.54 |
| 32 | 766.845 | 8.17× | 29.52 |
| 64 | **2526.656** | **26.93×** | 54.99 |

| 128 | **9306.238** | **99.2×** | 71.95 |

Exact quadratic through P ∈ {0,16,32}:

> **cost = 93.809 + 4.0506·P + 0.530681·P² M words**

Held out at P=64: predicted 2526.716 vs **actual 2526.656**, i.e. **+0.0024%**
— 24 parts per million, on a point 3.3× outside the fit range. **Held out again
at P=128 (2026-09-04): predicted 9306.970 vs actual 9306.238, +0.0079%** — 79 ppm
at 4× outside the fit range and 2× beyond the P=64 check. The quadratic is
confirmed, not merely consistent. Note the scale: a **2-instruction** loop with
128 never-executed neighbours costs **9.31 G words**, within ~4.7× of the muladd
mid-program cut's 43.8 G, reached from a trivial loop purely by table length. This is the
tightest held-out fit in this directory, and it is a genuine **exponent**, not a
constant factor. The quadratic term overtakes the linear one at **P = 7.6**, so
a program of more than ~8 instructions is already in the quadratic regime.

### 2.2 …and it needs the unknown counter. Pinning removes the exponent.

Same contract, same `|Σ|`, same chunks, same table, same steps; only `k = 5`
added to the path condition:

| P | unpinned | pinned | ratio |
|---|---|---|---|
| 0 | 93.809 | 5.789 | 16.2× |
| 16 | 294.473 | 6.289 | 46.8× |
| 32 | 766.845 | 6.859 | 111.8× |
| 64 | 2526.656 | 8.227 | **307.1×** |

The pinned arm is `5.777 + 0.0334·P` (held-out linear −3.77%), **1.42× over the
whole range**. So `composition-payoff.md` §2.4's pinning effect is not a 9.19×
constant — **it is a factor that grows linearly in program length**, and 9.19×
is its value at a 2-instruction program.

### 2.3 The flat unrolled VC of the same loop is linear and nearly free

`X1` pinned concrete, so exactly `N` trips execute.

| P | net M words (N=8) | vs P=0 |
|---|---|---|
| 0 | 15.646 | 1.00× |
| 16 | 17.835 | 1.14× |
| 32 | 20.115 | 1.29× |
| 64 | 25.004 | **1.60×** |

`15.631 + 0.1397·P`, held-out linear **−1.74%**. Slightly superlinear, but a
4-point series over a 1.6× effect cannot distinguish linear from quadratic and
**no exponent should be quoted**.

The prefix does, however, tax each *trip*: refitting the trip law at both ends
(N ∈ {8,16}),

| P | flat trip law | per-trip cost |
|---|---|---|
| 0 | `3.425 + 1.5277·N` | 1.528 |
| 64 | `4.245 + 2.5948·N` | 2.595 (**+69.8%**) |

so the prefix penalty is **not** a pure intercept shift. (The P=0 law reproduces
the published `3.410 + 1.5278·N` to 0.4% on the intercept and 0.007% on the
slope.)

### 2.4 A straight-line segment with symbolic values stays linear too

§2.1's rig, extended to K=64. Three *symbolic* register values (`x`,`y`,`z`),
three MVs, no branch:

| K | net M words | vs K=0 |
|---|---|---|
| 0 | 7.220 | 1.00× |
| 32 | 8.339 | 1.16× |
| 64 | 9.759 | **1.35×** |

**So symbolic values are not the trigger.** This arm carries three of them and
pays 1.35×. What the loop body has and this does not is a **branch whose
condition the solver cannot decide by computation** — in the loop body the BNE
tests `dec k ≠ 0`, which must be matched against the path-condition guard rather
than computed; pinning `k` (§2.2) turns exactly that match into a computation
and the exponent disappears.

### 2.5 Footprint moves too — the first arm in this family where it does

`composition-payoff.md` says of itself "this record says nothing about
footprint" because `top_heap_words` was byte-identical across every arm. On this
axis it is not.

| P | PB net RSS | PP net RSS | PF net RSS |
|---|---|---|---|
| 0 | 41.4 MB | 22.1 MB | 26.6 MB |
| 16 | 85.3 | 23.3 | 30.7 |
| 32 | 297.1 | 25.0 | 36.6 |
| 64 | **1317.7** | 29.9 | 50.1 |

**31.8×** on the composed arm against 1.35× and 1.88× on the others, and
`top_heap_words` finally steps off its floor (553,738,752 → 732,320,256) at
P=64. At P=128 net RSS is 3481.1 MB against P=64's 1317.7 MB — **2.64× for a 2× rise
in P, where quadratic would give 4×** — so the throughput law demonstrably does
NOT transfer to footprint (`top_heap_words` stepped again, 553,738,752 →
1,113,767,936). A quadratic fit on the RSS points holds out at only −7.1% and
produces a negative linear coefficient, so **do not quote a footprint
coefficient** — but
the axis is unambiguously superlinear, and it is a footprint driver, not just a
throughput one.

### 2.6 Control: conjunct order in the path condition is worth 1.74×

Not the point of the study, but it explains an apparent disagreement with the
published pinning ratio and is a reproducible effect in its own right:

| arm | pin position | net M words |
|---|---|---|
| `ZZPadP0` | before the guard | 5.789 |
| `ZZPadPrev0` | after the guard | 10.062 |
| `ZZCmpBodyPin` (published rig, re-run) | after the guard | 10.660 |

**1.74× from conjunct order alone.** So §2.4's 9.19× and this record's 16.2× are
both correct and differ only in where the pin sits. (`ZZPadPrev0` vs
`ZZCmpBodyPin` differ by 5.6%, which is my rig's `repeat … ++` table wrapper
being reduced by `vm_compute` — the two rigs are otherwise the same object.)
Compare the already-known conjunct-order cost bug in
`sep_contract_fetch_instr`; ordering effects in the path condition are a
recurring theme, not a one-off.

### 2.6b The payoff realised: a loop cut inside a 66-instruction program

`Example/PaddedLoop.v` is the countdown loop cut, verbatim, except
that the program is `List.repeat (MV X4 X4) 64 ++ cd_instrs` (66 instructions,
loop head at byte 256) and both segment contracts carry **only their own two
instructions**, with the offset in `cfg_placement`. Both close with a real `Qed`.

| arm | program | net M words |
|---|---|---|
| `PaddedLoop` (both segment contracts) | 66 instrs | **177.21** |
| published `CountdownComposed` (same cut) | 2 instrs | 177.96 |
| same cut with untrimmed tables (2 × `pbody` at P=64) | 66 instrs | ~5053 |

**The cut inside the 66-instruction program costs 0.42% LESS than the identical
cut in a 2-instruction program.** Program length has become free for the composed
proof, against ~28.5× for the untrimmed alternative. That is the whole point of
the exercise, and it is measured rather than projected.

The heavy half is **compiled, hole-free and axiom-clean** (`Print Assumptions
pl_loop` reports only `pure_decode` and `mmioenv`, the model's inherent
parameters). It owns `ptsto_instrs` of the **whole** 66-instruction program and
closes the table gap with `itable_faith_of_segment` at
`pre := pl_pre, seg := pl_seg, post := pl_post`, then gets the loop from
`myWP2_loop_induction`. Both files are now permanent and gate-checked:
`Example/PaddedLoop.v` + `Example/PaddedLoopResult.v`, with `pl_loop` in
`scripts/gate.sh`'s `AXIOM_CLEAN_THMS` — **the only proof in the tree whose
contract table covers a proper subset of the program**, hence the only check
that the sub-table path stays sound.

Figures above re-measured serially (177.21 M net, baseline 605,916,589), since
the first reading was taken while other work was building — 0.06% apart, so the
concurrency hazard in §0 did not bite here.

Two traps cost a compile each and are worth knowing before writing another
sub-table contract:

- **`list_AST_AnnotInstr` is `List.map AST_AnnotInstr`, NOT an identity**
  (`Verifier.v:145`; coqc even warns "not definitionally an identity
  function"). So a `list AST` cannot stand in for the `list AnnotInstr` that
  `ptsto_instrs` and `itable_rel` are stated over — the existing examples only
  get away with writing `cd_instrs` because the *contract field* coerces it. The
  failure is an unresolved-implicit error on `<$>` ("Cannot infer the implicit
  parameter M of fmap"), which reads like an Iris notation problem and is not
  one. Give the program an explicit `AnnotInstr`-level `pre`/`seg`/`post`
  decomposition and define `padded_annot := pl_pre ++ pl_seg ++ pl_post`; the
  lemma's `pre ++ seg ++ post` then matches SYNTACTICALLY, which also avoids an
  `app_nil_r` rewrite that would otherwise hit the `seg` occurrence inside
  `table_of_list` as well.
- **`itable_faith_of_segment`'s `pre`/`seg`/`post` are EXPLICIT.** `Set Implicit
  Arguments` marks only *strict* implicits and `length pre` is not a rigid
  position, so only `Σ`, `cbase` and `off` are implicit. `off` occurs in no
  explicit argument's type, so it cannot be inferred; and `(off := _)` fails
  with "Not enough non implicit arguments" unless every preceding explicit
  argument is supplied. Use the fully-`@` form:
  `@itable_faith_of_segment Σ p ι cbase off pre seg post`.

### 2.7 The lever, measured directly: a SUB-TABLE contract

The trimming fix is not a projection — it is the same dial read in the other
direction. `pseg off` is the identical loop-body segment (same precondition,
same guard, same post, same fuel, same executed steps) except that its table
holds **only the two instructions it executes** and the segment's byte offset is
carried by the **placement term** (`cfg_placement := term_val (bv.of_N off)`)
instead of by a prefix of filler in the table. `table_of_list p 0 seg` then emits
exactly the addresses `base+off`, `base+off+4` that `pbody`'s padded table emits
for those same two instructions.

| arm | table | net M words |
|---|---|---|
| `pseg` at offset 0 | 2 instrs | 93.788 |
| `pseg` at offset 256 | 2 instrs | **93.830** |
| `pbody` at P=64 (same segment) | 66 instrs | **2526.656** |

Two readings, both clean:

- **The placement offset is free: 0.045%.** Moving a segment from address 0 to
  address 256 costs nothing. So the K² term is entirely the *table*, not the
  addressing, and a sub-table contract at a nonzero offset pays the same as one
  at zero.
- **Trimming recovers the whole 26.93×.** `pseg 256` vs `pbody 64` is the
  identical segment differing only in what its table contains.

(`pseg 0` vs `pbody 0` agree to 0.02%, which is the consistency check that they
are the same object.)

**Soundness of this is now largely built** (2026-09-04, `Tables.v`): `itable_rel`
is a `List.Forall` over the *table's* entries asserting only that the map
*contains* each one, and `itable_faith_weaken` already lifts it along `m ⊆ m'`,
so the obligation reduces to three gmap containments —
`instrs_of_list_prefix`, `instrs_of_list_suffix` and their composition
`instrs_of_list_segment`:

```coq
instrs_of_list (base + 4·|pre|) seg  ⊆  instrs_of_list base (pre ++ seg ++ post)
```

That is the whole soundness content of "a contract that knows only the
instructions it executes". `etable_faith_exits_of_offs` needs no change — it is
already placement-relative.

## 3. Mechanism: the cost is TRANSIENT — the VC does not get bigger

### 3.1 Every structural count is invariant in P

`ZZLvarInstrCommon`'s `zz_all_raw` on the RAW (pre-`postprocess`) VC, at all
four prefix lengths:

| P | nodes | asserts | assumes | binders | vareqs | maxsig | sigint | occ | lw | (ang,dem,err,blk) |
|---|---|---|---|---|---|---|---|---|---|---|
| 0 | 236 | 42 | 32 | 73 | 70 | 7 | 257 | 24 | 47 | (15,29,15,30) |
| 16 | 236 | 42 | 32 | 73 | 70 | 7 | 257 | 24 | 47 | (15,29,15,30) |
| 32 | 236 | 42 | 32 | 73 | 70 | 7 | 257 | 24 | 47 | (15,29,15,30) |
| 64 | 236 | 42 | 32 | 73 | 70 | 7 | 257 | 24 | 47 | (15,29,15,30) |

**Byte-identical at every P** — every counter, including the branch structure
and the count of proof obligations. The pinned contract is likewise invariant
(224 / 38 / 30 / 69 / 67 / 6 / 179 / 10 / 17, (14,29,14,30) at all four).

So the 26.93× is **not a bigger VC**. The executor builds the same 236-node
object with the same 42 obligations and the same 15 error leaves, and pays 27×
more to do it. The K² is **entirely transient construction state**.

This is the second independent sighting of the phenomenon `base-k-hunt.md`
established for `Base(K)` ("the ENTIRE finished VC is ≤2.6% of peak heap, so
`Base(K)` is not tree-reachable at all — it is transient construction state").
That record had a *bound*; this one has an **exact invariance**, on a rig where
the driving parameter is a dial.

### 3.2 What is excluded

| candidate | why not |
|---|---|
| a larger VC / more obligations / more branches | §3.1 — every count identical |
| `var_dead`'s O(K) table scan | `drop_fuel = 0`; the drop is `pure tt` |
| `\|Σ\|` (quadratic per this directory's catalog) | `maxsig` = 7 and `sigint` = 257 at every `P`; `P` mints nothing |
| chunk count | identical at every `P` |
| executed steps | identical at every `P` (entry pc set past the filler) |
| lookup depth / occurrence count | `lw` = 47, `occ` = 24 at every `P` |
| symbolic values as such | §2.4 carries three and stays linear |
| program length alone | §2.3 / §2.4 / §2.5's pinned column all stay linear |

What is required is an **undecidable branch condition** *and* a **K-sized
instruction table**, together, and the product is spent and discarded during
construction. Note the instrument's own scope limit
(`footprint-vs-throughput.md` §2.5): it weighs formula and `vareq` payloads,
**not `AMessage` contents and not the symbolic heap** — so the unexplained mass
is, by construction, in the part it cannot see. `base-k-hunt.md` did ablate
`AMessage` snapshots and priced them at 1.7–2.1% of allocation, on the muladd
rig; if that transfers, the candidate list is thin and the remaining mass is in
per-step transport of the table through world extensions
(`persist`/`occurs_check`/`sub_comp`) rather than in anything retained.

### 3.2b REFUTED: the word column's O(K²) term size. Exactly quadratic, and FREE.

The strongest structural candidate, eliminated 2026-09-04 by ablation.

`words_ctx n` is ONE wide `bv (word·n)` variable and each address's instruction
word is a slice read off it by `words_of_slice` (`Verifier.v:1234`):

```coq
| S n' => cons (dtake word (words_width n') W)
               (words_of_slice ... n' (ddrop word (words_width n') W))
```

Entry `i` is therefore `take (drop^i W)` — **i nested `bvdrop` wrappers** — so the
column's total term size is quadratic. Measured exactly (`Example/ZZWordSize.v`):

| K | 8 | 16 | 32 | 64 | 128 |
|---|---|---|---|---|---|
| word-column term nodes | 44 | 152 | 560 | 2144 | 8384 |

which is **exactly `K(K+3)/2`** at every point. `peval` does **not** collapse the
nesting (identical sizes after `List.map peval`), so there is no take/drop
composition rule to lean on.

That is a genuine O(K²) structure, in the right variable, inside the object the
executor persists at every step. **It is nonetheless not the cost.** Ablating it
— every entry replaced by the *depth-0* slice, shared, so the column becomes O(1)
(`List.repeat (dtake word (words_width n') W) (S n')`, list length verified
preserved at 64 so `zip_words` cannot truncate) — moves nothing:

| P | ablated | original | Δ |
|---|---|---|---|
| 0 | 93.804 | 93.809 | −0.005% |
| 32 | 766.139 | 766.845 | −0.09% |
| 64 | **2524.939** | 2526.656 | **−0.07%** |

**So do not "fix" the word-slice nesting.** Removing the entire quadratic from the
representation is worth 0.07%, and de-nesting it properly would mean fighting the
width-index typing that `cfgver-executor` and `GenContract.v:536` both flag. The
ablation was temporary and unsound (every address gets the same word) and has
been reverted; the tree was rebuilt from the reverted source.

**Method lesson worth more than the result:** an exactly-quadratic structure, in
the same variable as an exactly-quadratic cost, in the object most obviously
implicated, was still not the cause. Matching exponents are not causation, and
the ablation cost ~15 minutes where building the de-nesting fix would have cost
days. Same shape as `ctx-fresh-cost.md`: bound the candidate before funding it.

### 3.2d The K² is BASE-INDEPENDENT — identical to four significant figures

Asked because every rig in §2 has a CONCRETE base while every real target
(`muladd`, `check_scalar`) has a symbolic one. Same loop-body segment, same
guard, same fuel, same table; the only change is `cfg_placement := term_var "p"`
with the base bound added to the precondition (`|Σ|` 1 → 2). **One protocol for
both arms** (`intros; vm_compute; solve_vc. Admitted.`), baseline 605,918,314:

| P | concrete base | symbolic base | sym/con |
|---|---|---|---|
| 0 | 82.634 | 101.302 | 1.226× |
| 16 | 281.828 | 305.978 | 1.086× |
| 32 | 752.695 | 782.242 | 1.039× |
| 64 | 2509.392 | 2549.633 | **1.016×** |

| base | fitted law (on P ∈ {0,16,32}) | held-out P=64 |
|---|---|---|
| concrete | `82.634 + 3.9598·P + 0.530613·P²` | **+0.0024%** |
| symbolic | `101.302 + 4.3052·P + 0.530444·P²` | **−0.0040%** |

**The quadratic coefficients agree to 0.03% (ratio 0.9997).** So the base
contributes a CONSTANT (~18.7 M on the intercept) plus a small linear increment
(3.96 → 4.31 M per instruction), and **nothing at all to the quadratic**. Its
relative penalty therefore *shrinks* as the program grows — 1.226× at P=0 down to
1.016× at P=64 — which independently reproduces `cfgver-executor`'s standing
finding that "the symbolic base is a shrinking constant-factor penalty, not the
driver", on a different axis.

Two consequences:

- **Base-relative address arithmetic is eliminated as the mechanism.** `peval_bvadd`
  folding `c ⊕ p` keys, the extra base variable, and the fetch-bound machinery
  are all absent from the quadratic.
- **Everything measured on the concrete rigs transfers to the symbolic targets**,
  for this axis. That was an open assumption in §2 and it is now checked.

Side benefit, since both protocols now exist on the same rig: comparing this
concrete arm with §2.1's `Qed` one, `Qed` moves the intercept (82.6 → 93.8) and
the linear term (3.96 → 4.05) but leaves the **quadratic coefficient at 0.5306
either way (0.013% apart)**. So the `Qed`/`Admitted` gap is a constant plus a
touch of linear and cannot distort an exponent — which is what licenses the
one-protocol comparison above.

### 3.2c What is now excluded, and what is left

Excluded by measurement or construction: a larger VC (§3.1), `var_dead`'s scan
(`drop_fuel = 0`), `|Σ|` (constant 7), chunk count, executed steps, lookup depth
and occurrence count (§3.2), symbolic values as such (§2.4), program length alone
(§2.3/§2.4), **the word column's term size (§3.2b)**, **base-relative address arithmetic and the base
variable itself (§3.2d)**, and — from an earlier session, on the *exit*-table
knob — per-entry-per-step persist cost, measured FLAT with an exactly linear
total (`cfgver-executor`'s backward-branch banner).

Two candidates survive, neither tested:

- **`lookup_instr`'s `List.find`** recomputes the loop-invariant `peval apc`
  inside the predicate, once per table entry (`Verifier.v:630`); `is_exit` does
  the same over the exit list. That is the `var_dead` `&&` shape exactly. It
  gives O(K) per lookup with a constant number of lookups, so on its own it
  predicts LINEAR — it cannot be the whole story, but hoisting the `let` is
  zeta-convertible and therefore nearly free to try.
- **Something in the consume/produce path inside `sexec_instruction`**, which is
  where the earlier session's search also ended ("what carries the quadratic is
  still unidentified — it lives in the ACTIVE consume/produce path, not in
  anything reachable from a contract"). Note `chunk_gc` filters every
  `encodes_instr` chunk each step, so the symbolic heap does *not* hold one chunk
  per instruction and heap size is not the K factor.

### 3.3 Why this rig matters beyond this question

`base-k-hunt.md` closed with "`Base(K)` needs OCaml heap profiling", having
eliminated four candidates and found no cheap Coq-level handle. **This rig is
that handle.** It is a 2-instruction executed segment, a 236-node VC, and a
single integer dial that moves cost by 27× with *every* structural counter held
exactly constant; arms compile in 10–17 s. Any hypothesis about transient
construction cost can be tested here in minutes instead of on a 282-instruction
muladd prefix, and a fix's effect is unambiguous because there is nothing else
moving.

## 4. Consistency check: the muladd mid-program cuts

`plans/PLAN-muladd-full.md` records that mid-program cuts on the 282-instruction
whole-function muladd collapsed to a bare `False` at **~43.8 G words**, with the
cause listed as unidentified after four refuted hypotheses.

Extrapolating §2.1's law to K=282 gives **43.4 G words** — 0.9% from the
observed figure. **See §4.2: that agreement is almost certainly
coincidental, and the mechanism rather than the number is what carries over.**

### 4.1 The MECHANISM is independently corroborated by that same record

`PLAN-muladd-full.md` reports, for the one segment that *does* verify:
`ZZSeg1`, entry offset 0, **1.099 G words, real `Qed`**, and — in its own words
— *"its two forward branches are decidable from the pinned public `m[0] = 63`"*.
The mid-program cuts that fail cut into loops with symbolic counters.

So on muladd, at an **identical** K = 282:

| segment | branches | cost |
|---|---|---|
| `ZZSeg1` | decidable | 1.099 G, verifies |
| mid-program cuts | undecidable | 43.8 G, bare `False` |

**39.9× apart at the same program length**, split by exactly the property this
record isolates on countdown. That is independent corroboration of the
*mechanism* — the regime split — on a different program, a different contract
builder, a symbolic base and a ten-cell inventory. (It is not a matched pair:
the two arms also differ in contract builder and entry offset, which is the
method error that record already flags. It corroborates the split; it does not
measure it.)

### 4.2 …and it makes the COEFFICIENT agreement almost certainly a coincidence

The same number cuts the other way, and against §4's headline. `ZZSeg1` sits in
the **linear** regime at K=282 and costs 1.099 G, where this record's linear-
regime arm (`ZZU5_K64`) costs 0.0098 G. Muladd's per-instruction constants are
therefore on the order of **100× countdown's**. If its quadratic coefficient
scaled anywhere near its linear one, the undecidable-branch cuts would land in
the thousands of G, not at 43.8.

**So the 43.4 G vs 43.8 G agreement in §4 should be read as luck, not as
support.** Downgrading it explicitly: what transfers is the regime split (§4.1,
well supported), not the law. The trimming payoff on muladd is **unmeasured**,
and the run named below is what would measure it.

**Treat this as a hint, not a result.**

### 4.3 The muladd trimming payoff, MEASURED — 3.03×, and (K/k)² does not transfer

Matched pair on muladd segment 1 (`ZZSeg1`'s contract: `gen_contract_rel`, entry
offset 0, `extra_exit_offs = [220]`, bound 1168, fuel 8, identical reg/mem specs
and identical `exitCond` function; `vm_compute; solve_vc; solve_symbase_fetch.
Qed.` in both arms). Baseline 606,236,136.

| arm | table | net M words |
|---|---|---|
| full table | 282 entries | **1098.54** |
| trimmed table | 56 entries | **363.10** |

**Ratio 3.026×** — trimming removes 67.0% of the segment's cost. The full arm
reproduces `PLAN-muladd-full.md`'s published 1.099 G exactly, which is the check
that the rig measures the intended object.

**The countdown-derived model over-predicts by 8.4×.** `(K/k)²` at K=282, k=56
predicts 25.35×; even a purely linear `K/k` predicts 5.04×. A two-point
decomposition `net(K) = Base + c·K` gives **c ≈ 3.254 M words per table entry**
and **Base ≈ 180.9 M**, so 83% of this segment's cost is its table and the rest
is its own content. (Two points cannot distinguish linear from anything else —
that split is a decomposition, not a fit, and **no exponent should be quoted
from it.**)

**This is consistent with §2.4's regime split rather than against it.**
`PLAN-muladd-full.md` states segment 1's *"two forward branches are decidable
from the pinned public `m[0] = 63`"*, so it sits in the **linear** regime, where
this record measures length at 1.35–1.60× on countdown. Muladd's per-entry
constant is ~100× countdown's (3.254 vs 0.0334 M), which is why the same regime
yields 3.03× here instead of 1.4×. **The quadratic claim remains COUNTDOWN-ONLY:
the muladd arms that would test it are the mid-program cuts, and those do not
verify at all.**

Residual confound, not eliminated: `gen_contract_rel` derives the exit *table*
from its `instrs` argument, so the fall-through exit entry moved (1128 → 224)
between arms. The `exitCond` *function* was pinned identical. Decoupling the exit
table would have required a hand-written contract and so reintroduced the
two-axis method error `PLAN-muladd-full.md` already flags. One entry in a small
exit table — plausibly negligible, **unverified**. Also: the 56th entry (offset
220) is in the trimmed table but never executed, so 55 entries is the true
minimum; untested. Footprint is unusable on this rig (peak RSS came out *lower*
for the baseline than for the trimmed arm — import-closure floor noise). A coefficient fitted on a 2-instruction
loop with `|Σ|`=1 and a two-register inventory has no business predicting a
282-instruction program with a symbolic base and ten memory cells, and agreement
this tight over a 4.4× extrapolation in K is more likely coincidence than not.
What it does justify is *promoting the K² mechanism to the leading hypothesis*
for that blowup, and the controlled test is direct: run one muladd segment
contract with its table trimmed to the segment's own instructions and see
whether the cost falls by ~(282/k)².

## 4.4 The undecidable-branch muladd arm, measured — 95.4x, and a 2x2

§4.3 could only measure a *decidable*-branch segment (3.03x). The undecidable
one is now measured too, on `ZZSeg2`'s mid-program cut at offset 220, and it is
the arm this record's law is about:

| | full table (282) | trimmed table (15) |
|---|---|---|
| `T0` havoc'd | 43,503 M, `False` | 456.16 M, `False` |
| `T0` pinned public | 1,231.66 M, `Qed` | 338.78 M, `Qed` |

- **Trimming is worth 95.4x** on the undecidable/unprovable arm — vs 3.03x on
  §4.3's decidable one, exactly the regime split this record isolates, now on
  the same program. Exponent implied: `log 95.4 / log(282/15) = 1.55`, i.e.
  superlinear and sub-quadratic, so **the countdown coefficient still does not
  transfer** even in the right regime.
- **Trimming on the PROVABLE arm is only 3.64x.** Pinning a register the segment
  branches/addresses on removes most of the same work, which is why the two axes
  are strongly sub-multiplicative: 95.4x and 35.3x alone, **128.4x** together
  where independence would predict ~3368x. Both reduce the same product (solver
  work on undecided values x table size).
- **Cost was not the blocker.** Both havoc'd arms give a bare `False`; trimming
  made it 95.4x cheaper to *discover* that. The blocker was the cut assertion
  havocking `T0`, which holds the public pinned `m[0] = 63` that a load address
  in the segment depends on. Full write-up: `plans/PLAN-muladd-full.md`.

## 5. What this means

- **§2.1's "prefix length is nearly free" is CORRECT BUT NOT GENERAL.** It is a
  measurement of a straight-line segment, and it does not transfer to a segment
  contract with an undecidable branch — which is what every loop-invariant body
  contract is. Scoped, not retracted; annotated in place in
  `composition-payoff.md`.
- **The ADDENDUM's cost law needs the same scoping.** "A symbolic segment
  contract costs ~83–99 M words almost regardless of what it contains" is the
  value at K≈2. It is 2.5 G at K=66. The law is flat in the segment's *own*
  content and quadratic in the *surrounding program*, and every contract behind
  that ~90 M figure lived in a 2–4 instruction table.
- **Composition's break-even grows quadratically with program length.** The
  body contract alone breaks even against the flat VC at **59 trips** at P=0 and
  **972 trips** at P=64 (a full cut, body + exit contract, is ~2× both, which
  recovers the published 114 at P=0). So the technique degrades fastest exactly
  where it was meant to help — long programs.
- **The actionable fix is per-segment table trimming. Worth 26.93× on this
  rig; MEASURED at 3.03× on the one real muladd segment that verifies — the
  (K/k)² model does NOT transfer (§4.3).** A segment contract currently
  carries `cfg_instrs` = the *whole* program; it only ever fetches from its own
  segment.
  **Payoff measured directly in §2.7 (26.93×, with the placement offset free at
  0.045%), and the soundness side is now partly BUILT** — the three gmap
  containment lemmas are proved in `Tables.v` as of 2026-09-04
  (`instrs_of_list_prefix` / `_suffix` / `_segment`), on top of what already
  existed: `itable_rel` is a
  `List.Forall` over the *table's* entries each asserting `m !! a = Some i`, so
  it is indexed by the table and merely *contained* in the map; and
  `TablesRel.v`'s **`itable_faith_weaken`** already proves
  `m ⊆ m' → itable_rel m tbl → itable_rel m' tbl`, while
  `itable_faith_of_list_aux` is already generalised over a running offset
  `off`. A segment contract's table is therefore faithful to the *whole*
  program's gmap by the lemma that exists. What is missing is plumbing: a
  sublist lemma (`instrs_of_list (cbase+off) segment ⊆ instrs_of_list cbase
  full`), the exit-table analogue, a segment offset threaded through the
  contract record, and the `EndToEnd` bridges that currently assume
  `cfg_instrs` *is* the program. Real work, but not a new theorem.
  **Scope, stated because it is easy to overreach:** trimming only pays for a
  contract in the quadratic regime. A flat whole-program VC has nothing to trim,
  and a decidable-branch segment gets ~1.35×.
- **It is also a footprint lever** (§2.5), which none of the other levers in
  `composition-payoff.md` are, so it plausibly bears on the `mlen`=2 memory wall
  and on `footprint-vs-throughput.md`'s `Base(K)` block. Note the two are
  measured on different rigs and their exponents differ (that record's muladd
  prefixes imply steeper than quadratic); **do not equate the coefficients.**
- **The cost is transient, so this is a lever on the class of driver nothing
  else in this directory can reach.** §3.1's exact invariance means no amount of
  pruning, classing or postprocessing the *result* can help; the win has to come
  from not doing the construction work, i.e. from a smaller K. That is the same
  conclusion `base-k-hunt.md` reached for `Base(K)`, arrived at independently.
- **Amdahl, per this directory's rule:** at P=64 the K² term is 2433 M of the
  2527 M total (96.3%). On this axis there is nothing else worth attacking.

## 6. Files / reproduction

Throwaway, gitignored, none in `_CoqProject`:

| purpose | files |
|---|---|
| shared definitions | `Example/ZZPadCommon.v`, baseline `ZZPadBase.v` |
| composed body, prefix axis | `Example/ZZPadB{0,16,32,64}.v` |
| pinned body, prefix axis | `Example/ZZPadP{0,16,32,64}.v` |
| flat unrolled, prefix axis | `Example/ZZPadF{0,16,32,64}.v`, `ZZPadFN16_{0,64}.v` |
| conjunct-order control | `Example/ZZPadPrev0.v` |
| straight-line comparison | `Example/ZZU5_K64.v` (new point on §2.1's rig) |
| sub-table arm (§2.7) | `Example/ZZPadS{0,256}.v` |
| P=128 point | `Example/ZZPadB128.v` |
| muladd trimming pair (§4.3) | `Example/ZZTrim{Base,F,T}.v` |
| the realised demo (§2.6b) | `Example/PaddedLoop.v`, `Example/PaddedLoopResult.v` (both PERMANENT, gate-checked); measurement baseline `Example/ZZPaddedLoopBase.v` |
| structural counts | `Example/ZZPadI{0,16,32,64}.v` + `ZZLvarInstrCommon.v` |
| word-column term size (§3.2b) | `Example/ZZWordSize.v` |
| base-independence (§3.2d) | `Example/ZZPadBA{0,16,32,64}.v` (concrete) vs `ZZPadSB{0,16,32,64}.v` (symbolic) |

```bash
OCAMLRUNPARAM='v=0x400' /usr/bin/time -f "RSS %M KB WALL %e s" \
  coqc -q -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp -R theories Katamaran \
  case_study/RiscvPmp/CFGVer/Example/<probe>.v 2>&1 \
  | grep -E 'allocated_words|top_heap_words|RSS|Error'
```

**Promoting the demo is DONE**: `Example/PaddedLoop.v` +
`Example/PaddedLoopResult.v` are in `_CoqProject`, re-exported from `Results.v`,
and `pl_loop` is in the gate's `AXIOM_CLEAN_THMS`. The four points previously
listed here as unchecked are discharged — the two that were real are written up
in §2.6b; the `app_nil_r` and `iExact`-position worries did not materialise.

Traps hit here:

- **`ZZLvarInstrCommon.vo` goes stale** against a rebuilt `Prelude.vo` and fails
  with *"makes inconsistent assumptions over library"* — exactly the trap
  `footprint-vs-throughput.md` §5 records. Rebuild it before the count arms.
  Without the `Error` grep these arms read as *free*.
- **Pad BEFORE, not after.** Padding after the loop puts a filler instruction at
  the fall-through address, so the branch that is infeasible at P=0 becomes a
  further executed step — a second axis silently added to the one under test.
