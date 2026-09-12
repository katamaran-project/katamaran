# PLAN — generators and combinators for COMPOSITIONAL segment proofs

Status: **layers 1–3 written and tracked (2026-09-09)**, `GenSegment.v` (light)
and `GenCompose.v` (heavy). This file records why they exist, what varies vs
what is fixed, and — importantly — what was deliberately *not* built.

Motivation, in the owner's words: *"a lot of time has been lost on proving
things by hand … basically the same idea as `gen_contract` for the
non-compositional setting, along with some specialised lemmas that solve the
composition for pre- and post-conditions of (largely) fixed shapes, some logic
might still be specific to the example sometimes."*

---

## 1. The duplication, MEASURED (muladd family, before this change)

| boilerplate | copies |
|---|---|
| the `PVExist/PVConst/PVBaseOff` register-assertion builder | **21** |
| its `fold_right … ⊤ specs` wrapper | **22** |
| `Proof. intros; vm_compute; solve_vc; solve_symbase_fetch. Qed.` — byte-identical | **31** |
| `itable_faith_of_segment` call sites | **20** |
| `etable_faith_exits_of_offs` call sites | **10** |
| the `exit_hit` Ltac | 3 |
| `rc_*` register-convert equations (`rc_T1` defined twice) | 19 |
| local `Definition S0..S3 : RegIdx` | **163 files** |

Root cause for the register half: **`gen_reg_asn_rel` is hardwired to
`["p"] ▻ "a"`**, while the *concrete* `gen_reg_asn` is already `{Σ}`-generic. A
cut needs extra logic variables (a counter, data pointers), so it copies the
builder — and copies it AGAIN for the `▻ "an"` post-context, because an
`Assertion` is indexed by its context and does not weaken.

That second copy is not just verbosity. Two definitions with identical bodies
are **convertible but not syntactically equal**, and `iFrame` matches
syntactically. That is precisely the wall that produced the misleading
`No applicable tactic` in *both* hand-written loops and cost the most time.

---

## 2. What is fixed and what varies

**Layer 1 — the segment contract (light).** Eight of ten fields are determined
by five numbers and a spec list:

| field | status |
|---|---|
| `place`, sub-table, exits, exitCond | shape fixed; vary only in `head`, `skip`/`take`, targets |
| pc-eq conjunct | **completely fixed** |
| base-bound conjunct | fixed given `bound` |
| register block | fixed given a `reg_spec_rel` list |
| the VC proof | **identical 31×** |
| `extra_pre` / `extra_post` | **genuinely per-segment** |
| fuel | a number (15–250 in use) |

`extra_pre`/`extra_post` is exactly the "logic still specific to the example".

**Layer 2 — table faithfulness (heavy).** Fully mechanical.

**Layer 3 — the loop (heavy).** Skeleton identical across both worked loops;
only three things vary — the invariant's index arithmetic, the branch guard,
and the resource shift.

---

## 3. The API

### `GenSegment.v` (light, after `GenContract.v`)

```coq
gen_reg_asn_at  {Σ} (base : Term Σ ty_xlenbits) : reg_spec_rel -> Assertion Σ
gen_regs_at     {Σ} (base : Term Σ ty_xlenbits) : list reg_spec_rel -> Assertion Σ
seg_exitCond    (ia : N) (targets : list N) : bv xlenbits -> bool
gen_seg_contract {Σ} (base : Term Σ _) (base_a : Term (Σ ▻ "a") _)
                 (ia head : N) (prog : list AnnotInstr) (skip take : nat)
                 (targets : list N) (bound : N) (fl : nat)
                 (regs : list reg_spec_rel)
                 (extra_pre : Assertion (Σ ▻ "a"))
                 (post : Assertion (Σ ▻ "a" ▻ "an")) : CFGVerifierContract
Ltac solve_seg
rc_X0..rc_S3 (24 equations) + Ltac reg_reduce
```

**The base is a TERM PARAMETER, not a `ctx.In "p" Σ` constraint.** No dependent
plumbing, the caller still writes `term_var "p"`, and — the point — ONE
definition serves the pre- and the post-context, so a single
`cbn [gen_reg_asn_at]` reduces both sides of an `iFrame`.

`base` and `base_a` are the same term at two contexts. Two arguments, because
`cfg_placement` lives at Σ while the precondition lives at `Σ ▻ "a"`. The
hand-written segments already paid this by writing the pc-eq term inline; the
alternative (`subst _ sub_wk1`) is recorded elsewhere as a Θ(|Σ|²) cost driver
and would put a non-transparent wrapper around every address.

`seg_exitCond` takes **absolute** byte targets, so single- and multi-exit
segments are spelled the same way. The hand-written segments used two different
spellings (`of_N (ia + 1128)` vs `of_N (ia + head + 108)`) — a latent source of
exit-table mismatches.

### `GenCompose.v` (heavy, after `Adequacy.v`)

```coq
split_id          {A} (m n) (L) : firstn m L ++ firstn n (skipn m L) ++ skipn (m+n) L = L
itable_faith_at   -- one lemma for all 20 Hif call sites
seg_exitCond_hit  -- In t targets -> seg_exitCond ia targets (of_N (ia+t)) = true
seg_exits_faith   -- one lemma for all 10 Hef call sites
seg_vc            -- projects ValidCFGVerifierContract past the stuck cfg_map
seg_entry/seg_exit -- the bundles the soundness bridge consumes / hands back
seg_step          -- ONE segment execution, with an explicit FRAME
seg_step1         -- single-exit specialisation; the pc is PINNED
seg_seq           -- SEQUENTIAL composition (what the straight-line cuts need)
seg_loop          -- myWP2_loop_induction + a hand-off to any continuation
```

**`split_id` is the good find.** Every hand-written `Hif` asserted
`length (firstn m L ++ firstn n (skipn m L) ++ skipn (m+n) L) = length L` and
closed it by `vm_compute` — computing a 282-element list, eight times over. It
is an *identity*, provable in one line with no numbers:
`rewrite <- drop_drop, take_drop, take_drop.` (46 ms). `itable_faith_at` then
discharges the real `HifDv` goal by `eapply … ; [reflexivity | vm_compute; lia
| exact Hp | exact Hrep]`.

`itable_faith_at` carries `4 * skip = head` as a **proof obligation**, which
turns GenSegment's head/skip agreement from a silent convention into something
that cannot pass unnoticed.

**`seg_step` is the centrepiece.** It reduces one segment execution to two
ordinary iProp implications:

```coq
(HPre  : Pre -∗ Fr ∗ seg_entry c iota a L cbase)
(HPost : forall an, Fr ∗ seg_exit c iota a L cbase an -∗ Post)
⊢ Pre -∗ myWP2_loop Post
```

Everything else — the `iApply sound_scfg_verification_condition_myWP2`, the
`$!` instantiation, the `with "[...]"` selector, the `destruct an`, the
exit-address `assert`, and the `⌜secLeak a⌝` side goal (trivial: `a` is a plain
bitvector, hence always `SyncVal`) — is inside the combinator and never appears
at a call site again. Verified by applying it to the existing `dv_step`: the
`Hif`/`Hef` goals fall to the layer-2 lemmas and the two remaining obligations
are exactly `HPre`/`HPost`.

`Fr` is an explicit **frame**: not selected by the bridge's selector, so it
survives untouched into the continuation. Making it a parameter is what lets a
segment be dropped mid-chain without restating the registers and memory it does
not touch.

**`seg_seq` is the one most of the remaining work needs.** Nine of muladd's
fourteen segments are straight-line: they do not want `seg_loop` at all, they
want A's postcondition chained into B's precondition, which is what the tail
spelled out per link as `linkN`/`linkFN`. It is five lines over
`myWP2_loop_bind` — and precisely the kind of wrapper that otherwise gets
re-derived at every call site, which is how the 21 copies of the register
builder happened in the first place.

`seg_loop` hands off to an arbitrary continuation rather than terminating the
proof — the difference between a loop lemma usable mid-function and one usable
only for the last segment. (`am_loop` hardwired its conclusion to `sgN`'s exit
condition and so could not be reused.)

---

## 3b. THE pc, standardised (2026-09-09, second pass)

Everything about the pc turned out to be standardisable too, and it was the
largest pocket left. Two distinct problems, measured across the live
compositional files:

| pc boilerplate at call sites | count |
|---|---|
| `destruct an as [av\|..]; [\|contradiction]` | 6 |
| `assert (Hav : av = ...)` via `bv.eqb_spec` + `congruence` | 6 |
| `unfold <seg>_headExitCond / _exitCond` | 13 |
| `rewrite <- bv.of_N_add` (address normalisation) | 7 |

**(a) Two spellings of the same address.** `bv.add (bv.of_N ia) (bv.of_N off)`
— what `inst place iota` produces, since a placement is `p +b of_N head` — and
`bv.of_N (ia + off)`, what `seg_exitCond` compares against. 30 and 24
occurrences respectively, and any proof meeting both pays a `bv.of_N_add`
rewrite. Fixed by a canonical form in `GenSegment.v`:

```coq
Definition seg_addr (ia off : N) : bv xlenbits := bv.of_N (ia + off).
Lemma seg_addr_add : seg_addr ia off = bv.add (bv.of_N ia) (bv.of_N off).
```

**(b) Exit-address resolution.** `seg_exitCond_hit` (a declared target IS hit)
was already there; its CONVERSE was not, and that is what every call site was
open-coding:

```coq
Lemma seg_exitCond_inv  : seg_exitCond ia targets v = true ->
                          exists t, In t targets /\ v = seg_addr ia t.
Lemma seg_exitCond_inv1 : seg_exitCond ia [t] v = true -> v = seg_addr ia t.
```

Only a declared target is reachable, so the exit condition PINS the pc. With
`inv1`, `seg_step1` removes the whole ritual from the call site: no `forall
an`, no SyncVal-vs-NonSyncVal destruct, no `unfold …exitCond`, no
`bv.eqb_spec` assert, no `subst`. `Hec : cfg_exitCond c = seg_exitCond ia [t]`
is `eq_refl` for any contract `gen_seg_contract` built with a one-element
`targets`.

All the pure exitCond algebra lives in `GenSegment.v` next to `seg_exitCond`
(no Iris in any of it); `GenCompose.v` keeps only `seg_exit_at` / `seg_step1`.

Multi-exit segments (muladd's `sgL` declares two) still use `seg_step` and
`seg_exitCond_inv`, whose `In t targets` destructs to the disjunction — one
`destruct` instead of a hand-rolled `bv.eqb_spec` chain per target.

---

## 3c. BOUNDS, and one correctness-by-construction fix (2026-09-10)

### The three bounds are not independent

Every compositional lemma threaded three hypotheses by hand — **24
re-declarations across ~14 lemmas** (12 `Hrep`, 9 `Hlen`, 3 `Hmax`), plus 29
mentions of `bv.exp2 xlenbits`, 5 inline copies of the
`change (bv.exp2 xlenbits) with 4294967296%N` incantation, 8 `bv.bin_of_N_small`
rewrites and 4 `bv.add_cancel_*` chains.

They collapse. `maxAddr = minAddr + lenAddr` and **`minAddr = 0`**, so `Hmax`
and `Hlen` are the *same fact* in N and in Z; and `Hrep` follows from either
plus `lenAddr_rep`, provided the segment fits inside `bound` (which it does by
construction — `bound` is chosen ≥ the program's byte length). So the caller
supplies ONE natural fact and the rest are projections:

```coq
Definition seg_wf (ia bound : N) : Prop := (ia + bound <= lenAddr)%N.

seg_wf_bin  : bv.bin (bv.of_N ia) = ia            (* ia is not truncated *)
seg_wf_max  : bv.bin (bv.of_N ia) + bound <= maxAddr
seg_wf_Z    : bv.unsigned (bv.of_N ia) + Z.of_N bound <= Z.of_N lenAddr
seg_wf_rep  : 4*|L| <= bound -> bv.bin (bv.of_N ia) + 4*|L| < bv.exp2 xlenbits
```

Each is two or three lines. The point is not the lines saved but that a caller
no longer has to know *which of three shapes* a given lemma wants.

### Address lemmas the sliding loops will each need

```coq
seg_addr_bin  : off <= bound -> bv.bin (seg_addr ia off) = ia + off
seg_addr_neq  : o1,o2 <= bound -> o1 <> o2 -> seg_addr ia o1 <> seg_addr ia o2
seg_addr_step : seg_addr ia off +b bv.of_N d = seg_addr ia (off + d)
Ltac bv_bound := pose proof exp2_xlenbits; lia.   (* see the port's traps, §5 *)
```

`seg_addr_neq` is the non-aliasing obligation every sliding-window loop body
owes; the tail proved it inline as `bv_off_neq` with a
`bv.add_cancel_l`/`_r` + `bin_of_N_small` + `lia` chain. `seg_addr_step` is the
tail's `bv_shift4` with the hardcoded `d = 4` generalised. D, I and K will each
have wanted both.

### minimal_pre: closing an asymmetry that WAS a bug

`CFG_VC_triple` already wraps the precondition in `extend_to_minimal_pre`, but
the postcondition was left to the caller. A post that forgets to hand
`cur_privilege` / `inv_leakage` back consumes them on every trip, so the loop
body can only ever run ONCE — which is exactly what happened to `amBody_post`,
and it fails late and confusingly. `gen_seg_contract` now appends
`∗ minimal_pre` itself, so the post mirrors the pre and the mistake is not
expressible. Re-validated: segment G's VCs still close with `solve_seg` alone.

---

## 3d. THE PORT, and what it found (2026-09-10)

`Example/ZZMladDvLoop2.v` is segment G composed **through** the machinery:
same theorem as the hand-written `ZZMladDvLoop.v`, but nothing open-codes the
soundness bridge. It compiles clean in 47.8 s, 12 `Qed`, no holes,
`dv_loop_31` axiom-clean (only `Machine.pure_decode`, `Base.mmioenv`).

Like-for-like against the hand-written path:

| | files | total lines | code lines | `Qed` |
|---|---|---|---|---|
| hand-written (`DvBody` + `DvFinal` + `DvLoop`) | 3 | 797 | 563 | 22 |
| generated (`DvGen` + `DvLoop2`) | 2 | 441 | 343 | 14 |

Eight of the fourteen removed `Qed`s are the `rc_*` register table, which
moved to `GenSegment` in the previous commit — the port is what let the call
site actually stop declaring it. What the port itself removed:

- `HifDv`/`HifDvf`, 25 lines each with a **per-call 282-element `vm_compute`**,
  become 6 lines each on `itable_faith_at` (the `vm_compute` is gone: `split_id`
  makes reassembly an identity).
- `HefDvBody`/`HefDvFinal` plus the copied `exit_hit` Ltac (12 + 12 + 5) become
  6 lines each on `seg_exits_faith`.
- The whole `pose proof valid_… ; unfold ValidCFGVerifierContract, Valid_CFG_VC,
  CFG_VC_triple ; iApply (sound_scfg_verification_condition_myWP2 … $! … with
  "[…]")` ritual, and the `forall an` / `destruct an` / `bv.eqb_spec`
  exit-resolution block: gone, into `seg_step1`.
- `dv_loop`'s body is now literally `apply (seg_loop …)`.

### What the port ADDED — CORRECTED 2026-09-10 after measuring

Two things only a real call site could have surfaced. The first write-up of
this section got the second one wrong; both versions are below because the
correction is the more useful fact.

**1. HPre needs no register reduction at all.** Because `dvWinAsn` uses the
generator's own `gen_regs_at` (not a local copy) at the *same* valuation as the
contract's precondition, the register block, `T4`, the `secLeak` fact, the base
bound and `minimal_pre` are literally the same terms on both sides and frame
WHOLE. The hand-written `iDestruct … as "(Hr1 & … & Hr11)"`-with-exact-arity
plus `reg_reduce` plus a blanket `cbn` does not appear.

**2. Crossing a cut needs ONE lemma — not three, and not a tactic.** Across a
cut the valuations DIFFER (counter decremented, `"an"` bound). I claimed
`iFrame` therefore refuses the blocks and added three lemmas. **Measured, and
two of the three were unnecessary:**

| conjunct | bare `iFrame` | |
|---|---|---|
| `gen_regs_at (term_var "p") dv_regs` | **succeeds, 0.6 s** | lemma deleted |
| `minimal_pre` | **succeeds, 0.8 s** | lemma deleted |
| `T4 ↦ᵣ …` | **fails** — `iFrame: cannot frame` | needs the lemma |

`iFrame` matches convertible-but-not-syntactic assertions here after all. What
it genuinely cannot cross is a register whose **value** changed — which is the
one thing a segment is for. So `GenCompose` §5 keeps exactly:

```coq
asn_regidx_pts_inst : inst t1 i1 = inst t2 i2 ->
  asn.interpret (asn_regidx_pts r t1) i1 ⊣⊢ asn.interpret (asn_regidx_pts r t2) i2
```

stated across two contexts `R1`/`R2` because that is the cut situation (pre at
`Σ ▻ "a"`, post at `Σ ▻ "a" ▻ "an"`). Its premise is exactly the segment's
arithmetic — here `dv_dec`, the head's `addi T4,T4,-1` — so the program content
ends up isolated in one hypothesis and everything else is plumbing.

`gen_regs_at_inst` and `minimal_pre_inst` were proved, then deleted unused.
Re-derive them (12 lines) only if a real failure appears — plausibly a
`PVBaseOff` register under a base whose value is not pinned identically on both
sides. Do not add them back on the strength of the argument alone; that
argument has now been measured false once.

### PERFORMANCE: split the goal before framing (2026-09-10)

Not a detail — it was the file's dominant cost. `iFrame` searches every
conjunct of the goal for each named hypothesis, so framing the ambient
resources while the generated blocks are still in the goal is expensive:

| | |
|---|---|
| `iFrame "HF Hpc Hnpc Hinstrs"` over the whole goal | **46 s** (54 s if `cbn` runs first) |
| of which `iFrame "Hinstrs"` (the 282-instruction store) | 2.9 s |
| of which `iFrame "HF Hpc Hnpc"` | **66 s** |
| `iFrame "Hpc"` alone | **did not finish in 300 s** |
| `iSplitR "HF Hpc Hnpc Hinstrs"; [\| iFrame]` | **0.16 s + 0.35 s** |

So the instruction store is NOT the problem, and framing fewer hypotheses at a
time is *worse*. Peel the ambient half off with a split first. Whole-file
effect: `ZZMladDvLoop2.v` **47.8 s -> 28.5 s**, which makes the generated proof
faster than the hand-written one it replaces (36.4 s in the same run).

The hand-written `ZZMladDvLoop.v` recorded this trick in a comment
("Isolate the dvWinAsn conjunct FIRST: with it in the goal, iFrame tries to
unify every named hypothesis against that big unreduced term") and the first
port dropped it. Worth reading the proof you are replacing for its comments,
not just its structure.

### Two API facts confirmed

- `seg_step1`'s argument order works: one `apply` with `eq_refl` for `Hec`
  leaves exactly HPre and HPost, in 7 ms.
- ~~`Post` must be a **parameter** of the per-trip lemma, not fixed to the
  invariant: `myWP2_loop` has no monotonicity lemma.~~ **RETRACTED 2026-09-11.**
  No such lemma EXISTED, but it is a two-line corollary: `myWP2_loop` is a
  monad in its ExitCond, `exitCondImpliesMyWP2_loop` is the unit and
  `myWP2_loop_bind` the bind, so
  `myWP2_loop_mono (H : P -∗ Q) : myWP2_loop P -∗ myWP2_loop Q` follows
  immediately (56 ms). It is now in `GenCompose.v` §4. See §3i.

### Two fixes the port forced

- **`gen_seg_contract`'s `prog` is now `list AnnotInstr`, not `list AST`.**
  `cfg_instrs` is an `AnnotInstr` list, so with `list AST` the coercion lands
  OUTSIDE the slicing (`list_AST_AnnotInstr (firstn take (skipn skip prog))`)
  and can never unify with `itable_faith_at`'s `firstn take (skipn skip L)`.
  Callers with a `list AST` program are unaffected — the coercion just fires at
  the argument instead.
- **`bv_bound` is now `pose proof exp2_xlenbits; lia`.** See §5.

### 3e. THE FOUR FAITH LEMMAS ARE GONE (2026-09-10)

The port left segment G's composition proof with 90 of 243 code lines still
mechanical, and the largest single block was four named faithfulness lemmas --
`HifDvBody`/`HifDvFinal` (BYTE-IDENTICAL except the contract name) and
`HefDvBody`/`HefDvFinal` (differing only by the target list). 45 lines whose
only content was the numbers `135 27 540 1168` and the target list, every one
of which the caller had ALREADY passed to `gen_seg_contract`.

Their four bullets were three DECIDABLE side conditions plus `seg_wf`:

| bullet | old discharge |
|---|---|
| `4 * skip = head` | `reflexivity` |
| `skip <= length prog` | `vm_compute; lia` |
| `4 * length prog <= bound` | `vm_compute; discriminate` |
| `Forall (head <=) targets` | `constructor; [lia \| constructor]` |

Two of those are tactics, which is the whole reason the obligations had to
become named lemmas rather than inline arguments. `GenSegment.seg_ok prog skip
head bound targets : bool` bundles all four into one boolean, with four
projections (`seg_ok_off/_skip/_sz/_tgts`), and `GenCompose.seg_itable_faith` /
`seg_etable_faith` take exactly `(Hok, Hp, Hwf)` / `(Hok, Hp)`. Both are then
terms, so both obligations go INLINE into the `seg_step1` application:

```coq
apply (seg_step1 (dvBody ia) (dvI ia (m + 1)%N) (seg_addr ia 540) mlad_ai
         (@bv.of_N xlenbits ia) F ia 540%N eq_refl (valid_dvBody ia)
         (seg_itable_faith (cfg_placement (dvBody ia)) (dvI ia (m + 1)%N)
            ia mlad_ai 135 27 540%N 1168 [540%N] eq_refl eq_refl Hwf)
         (seg_etable_faith (cfg_placement (dvBody ia)) (dvI ia (m + 1)%N)
            ia mlad_ai 135 540%N 1168 [540%N] eq_refl eq_refl)).
```

45 lines and 4 `Qed`s out, 8 lines in: `ZZMladDvLoop2.v` 242 -> **204 code
lines**, 11 -> 7 `Qed`. Leaves exactly HPre/HPost in 24 ms.

Three things worth knowing before reusing this:

- **`place` and `iota` must be written out; `L` too.** `apply` elaborates an
  argument bottom-up BEFORE propagating the expected type into it, so an `_`
  there leaves `eq_refl`'s type as `seg_ok ?L ... = seg_ok ?L ...` (or `inst
  ?place ?iota = inst ?place ?iota`) and elaboration fails with a message that
  looks like the lemma is wrong. `take`, and only `take`, may be `_`.
- **`eq_refl` for `Hok` is FREE; a `vm_compute` lemma is not an improvement.**
  Discharging `seg_ok mlad_ai 135 540 1168 [540] = true` by kernel conversion
  reduces `length` over a 282-element `map`, four times per file. Measured
  against the obvious alternative (two named `Lemma ... = true` proved by
  `vm_compute; reflexivity`, passed in place of the `eq_refl`s): 32.84 s vs
  28.99 s, i.e. no reason to write the lemmas.
- **The change is line-count-only. It does not make the file faster.** Three
  interleaved runs each (coqc, matched): before 31.24 / 27.70 / 27.83 s, after
  28.99 / 30.75 / 27.62 s. The run-to-run spread is +-3 s and swamps any
  effect; do NOT quote a speed-up. (The first post-change run read 34.9 s and
  was a cold-cache artefact.)

Gate: PASSED 4m47s at `GATE_JOBS=1 GATE_PROBE_BATCH=18`, 18 theorems
axiom-clean. Note step 1 reports both `Results.vo` and `GenCompose.vo` up to
date -- `GenSegment.v`/`GenCompose.v` are outside `Results.vo`'s closure and
`GenCompose.vo` is in `BUILD_TARGETS` only because of that.

**Still open, and it is the same shape one level up.** What survives per call
site is ~12 lines: `seg_step1`'s own `(c, iota, a, L, cbase, Fr, ia, t)` plus
the two faith terms, and `ia mlad_ai 135 (27) 540 1168 targets` is written
THREE times in it. A `SegSpec` record (`ss_base/ss_base_a/ss_ia/ss_head/
ss_prog/ss_skip/ss_take/ss_targets/ss_bound/ss_fuel/ss_regs/ss_pre/ss_post`)
with `seg_contract : SegSpec Sigma -> CFGVerifierContract Sigma` and a
`seg_step1_spec` over it would take those 12 lines to ~2, and would matter
about 11 more times in muladd. Not built: it changes `gen_seg_contract`'s call
convention, and the projections (`ss_prog s` vs `mlad_ai`) are convertible but
not syntactically equal -- which is exactly the class of thing that has cost
iFrame time twice in this family already, so it needs measuring, not
reasoning.

### A build note for the ZZ probes (cost 3 dead ends today)

`ZZ*.v` files are NOT in `_CoqProject`, so `make -f Makefile.coq
<...>/ZZFoo.vo` silently has no rule and reports success having done nothing,
and `rocq_compile_file`'s dune fallback writes its `.vo` into
`_build/default/` while leaving the source-tree `.vo` stale. A dependent file
then reports `The reference seg_wf was not found in the current environment`
-- the stale-`.vo`-drops-names signature again, from a build that said it
succeeded. Compile a probe with `coqc` directly, passing `_CoqProject`'s two
load-path lines (`-Q case_study/RiscvPmp Katamaran.RiscvPmp -R theories
Katamaran`).

### 3f. RE-BASING A SEGMENT ON ITS OWN CODE BASE (2026-09-10, measured at the M->N cut)

A segment contract should not have to name the whole program's base and its own
byte offset. Re-based on its own `q` at `iq = ia + head`, FIVE of the seven
contract fields lose both:

| field | today | re-based |
|---|---|---|
| `cfg_init_addr` | `(ia + head)%N` | `iq` |
| `cfg_placement` | `base +b of_N head` | `term_var "q"` |
| pc-eq in the pre | `a = base_a +b of_N head` | `a = term_var "q"` |
| `cfg_exits` | `exits_of_offs place (map (fun t => t - head) targets)` | `exits_of_offs q targets` |
| `cfg_exitCond` | `seg_exitCond ia targets` (ABSOLUTE targets) | `seg_exitCond iq targets` |

`head` and `skip` then survive only in `seg_ok` / `itable_faith_at` -- the
composition side, which is where "how this segment sits in the program"
belongs -- and the `map (fun t => t - head)` disappears because the targets are
already what `exits_of_offs` wants.

**The experiment: the M->N cut (amFinal -> sgN), the one place a base-relative
pointer crosses a cut.** Probes `Example/ZZRebaseN.v` (117 lines, light) and
`Example/ZZRebaseCut.v` (97, heavy), both green.

**Result 1 -- a re-based contract VERIFIES.** `sgN` re-based on a code base
`"r"` (= p+1108) with the spill base as a separate logic variable `"d"`
(= p+1128) is discharged by plain `solve_seg`; `solve_symbase_fetch` copes with
two independent symbolic bases, each carrying its own address-space bound
conjunct. NON-VACUITY CHECKED: delete one of the four spill cells from the
precondition and it fails with `No applicable tactic`, so the five instructions
really are executing and really do need the cells.

**Result 2 -- the cut becomes a PURE FRAME, and a simpler one than today's.**
`cut_MN` hands amFinal's post (code base `q` = p+1056) to sgN's pre (code base
`r` = p+1108) with a single `iFrame`, 4.8 s, consuming X2, the `secLeak`, all
four spill cells, the register block and `minimal_pre`. Three PURE residues
remain -- the pc equation and the two bounds -- which is EXACTLY what
`ZZMladTail.linkFN` is left with today. It works because, re-based, not one
conjunct of the cut assertion mentions a code base: they are stated against the
shared data base or are base-free.

**Result 3 -- and this is the condition on the whole thing. Base-relative DATA
must move onto its own base at the same time.** Every base-relative item in the
muladd specs sits at offset >= 1128, i.e. past the 1128-byte code: registers
`A0 = p+1128`, `A2 = p+1140`, `X2 = p+1168`/`p+1152`, and every
`mem_spec_rel` cell (1128..1164). These are DATA addresses; they have nothing to
do with where a segment starts. Hang them off the code base and re-basing
breaks the cut. Measured, both halves:

- `X2 |-> q+96` vs `X2 |-> r+44` (equal values, different bases):
  **`iFrame` silently does nothing.** Fixable with `asn_regidx_pts_inst`
  (314 ms) but it costs ~14 lines per register per cut -- the premise restates
  both terms and both valuations in full. The premise itself is
  `cbn; rewrite <- !seg_addr_add; unfold seg_addr; f_equal; f_equal; lia`
  (28 ms). NOTE `rewrite <- !bv.of_N_add` does NOT work here (it rewrites the
  inner `bv.of_N (ia+1056)` forward and `lia` then dies on
  `bv.of_N ia + bv.of_N 1056 = bv.of_N ia + bv.of_N 1108`); go through
  `seg_addr_add`.
- the same for a memory cell (`q+96 |->m mv` vs `r+44 |->m mv` under
  `asn.exist "mv"`): **`iFrame` does nothing, and `asn_regidx_pts_inst` does
  not apply** -- it is about `asn_regidx_pts`, and there is an existential
  binder in the way. A new lemma would be needed, and there are four such cells
  at this one cut.

With the shared data base instead, both cross on a bare `iFrame` (224 ms, 2
lines) because both sides say the same term at valuations that agree.

**No performance argument -- do not claim one.** `peval` already flattens the
nested add: `peval ((p +b 540) +b 4) = term_val 0x220 + term_var "p"`. Fetch
addresses inside a segment are the same term size either way. The case for
re-basing is that the contract becomes self-contained, nothing more.

**What it costs to build:** a re-based generator (no `head`), `itable_faith_at`'s
`Hp` restated in `seg_addr` form so it stays `reflexivity` at the call site,
`seg_addr_rebase : seg_addr (ia+h) t = seg_addr ia (h+t)` for handing the pc
across, and `seg_wf_shift : seg_wf ia bound -> h + b' <= bound -> seg_wf (ia+h) b'`.
All small. The real work is re-pointing `mlad_reg_specs_rel` / `mlad_mem_specs_rel`
at a data base, which is a change to the muladd spec block, not to the machinery.

**One thing that did NOT get solved and will be hit again:** the spill block had
to be written TWICE in the probe (once at `nCtx > "a"`, once at
`mCtx > "a" > "an"`), because the cell address mentions the base and sits under
`asn.exist "mv"`, so a `Term Sigma` parameter would need weakening and the only
weakening to hand is `subst _ sub_wk1` -- a recorded Theta(|Sigma|^2) driver.
This is the same wall `GenSegment.v` documents for a generic memory-block
builder. A shared data base makes the DUPLICATION more visible, not worse.

### 3g. GENERATING BOTH SIDES OF A CUT -- the framing does collapse (2026-09-11)

Goal stated by the owner: minimise MANUAL WORK, not run time; each segment
verified independently and reusable; and `gen_contract` (or a slight adaptation)
used for the pre- AND post-condition at a cut, in the hope that the framing then
disappears. Measured on the M->N cut. Probes `ZZRebaseN.v` (118) +
`ZZRebaseCut.v` (88), both green.

**It is not a hope, it is a mechanism.** `iFrame` matches SYNTACTICALLY. Two
convertible copies of an assertion do not match; ONE Sigma-generic definition
applied at two contexts does. That is precisely why `gen_regs_at` was built, and
why registers already cross a cut for free. Extending it to the whole cut:

```coq
Definition gen_mem_at {Σ} (base : Term Σ ty_xlenbits)
    (specs : list (N * Term Σ ty_xlenbits)) : Assertion Σ := …
Definition gen_cut_at {Σ} (base : Term Σ ty_xlenbits)
    (regs : list reg_spec_rel) (mems : list (N * Term Σ ty_xlenbits))
    : Assertion Σ :=
  ( gen_regs_at base regs ∗ gen_mem_at base mems
    ∗ asn.formula (formula_secLeak base) )%asn.
```

A cut is then DATA -- one base, one register spec list, one memory spec list --
and the producing segment's post and the consuming segment's pre are the same
application of it. **Result: the cut hand-off is `iIntros "(Hcut & Hmin)"` and
`iFrame`.** Packaged:

```coq
Ltac solve_cut cpost cpre :=
  unfold cpost, cpre, extend_to_minimal_pre;
  cbn [cfg_postcondition cfg_precondition];
  iIntros "(Hcut & Hmin)"; iFrame;
  cbn; repeat iSplit; try done; iPureIntro; assumption.
```
and the whole cut is `Proof. solve_cut m_cut sgN_reb. Qed.`

Against what it replaces -- the hand-off half of `ZZMladTail.linkFN`, same cut,
same content: **10 lines -> 1**, two `unfold` chains (8 and 4 definitions) -> 0,
a six-way `iDestruct` -> a two-name `iIntros`. Everything after the `iFrame` is
NOT framing: it is the three pure residues every cut has (the pc equation and
the two address-space bounds a postcondition may not claim), and `linkFN` is
left with exactly the same three.

**What had to be solved to get there: the memory builder.** `gen_mem_asn_rel`
puts the cell value under `asn.exist "mv"` while the address mentions the base,
so a `Term Σ` parameter needs weakening -- `subst _ sub_wk1`, the recorded
Theta(|Σ|^2) driver -- which is why `GenSegment.v` deliberately has no memory
builder. The way through is the one that comment itself names: **take the cell
VALUES as parameters so the builder never extends the context.** The values then
live in Σ and the composition existentially quantifies them at the iProp level,
exactly as `dvInvN` already does for its counter.

**The cost of that, MEASURED, and do not over-read it.** Moving four cell values
into Σ takes sgN's context from 2 to 6 variables. Matched `-time` runs of the
same VC: `solve_seg` 0.878 s -> 0.918 s, `Qed` 0.629 s -> 0.634 s. Invisible.
BUT this is a 5-instruction segment with 4 cells, and |Σ| is the measured
QUADRATIC driver ([[project-lvar-lookup]]) -- a 27-instruction segment carrying
16 cells is a different question and has not been measured. Do not quote 4.5%
as "the cost of values-in-Σ".

Non-vacuity checked on the values-in-Σ form too: drop one cell from `cutMems`
and `solve_seg` fails with `No applicable tactic`.

**Still hand-written after this, at a cut:** nothing, for the spatial part. What
remains per cut is the pc equation and the bounds, both pure and both already
one `assumption` inside `solve_cut`. What remains per SEGMENT is the invariant
itself -- which is the specification, and should stay hand-written.

### 3h. WHAT IS LEFT AT A CUT (2026-09-11)

Three things assumed in 3g were TESTED this round, and one more was removed.

**Tested and true:**
- **The realistic two-contract form works.** `cut_MN` now goes
  `cfg_postcondition (amFinal_reb …) |- extend_to_minimal_pre
  (cfg_precondition (sgN_reb …))`, i.e. contract to contract, and is still
  `Proof. solve_cut amFinal_reb sgN_reb. Qed.`
- **Variable NAMING is not load-bearing.** amFinal calls the data base `"sp"`
  and the cells `"s0".."s3"`; sgN calls them `"d"` and `"m0".."m3"`. The cut
  still frames. Segments are therefore independently nameable -- no global
  convention, which is a precondition for reusing one.

**Removed this round: the per-cut address-space bounds.** `seg_wf_shift`
(a sub-segment of a well-formed segment is well-formed) plus the `seg_bound`
tactic, both in `GenSegment.v`, derive every segment's and every data block's
bound from the program's ONE `seg_wf ia bound`. `cut_MN` went from two
hand-threaded hypotheses (`Hr`, `Hd`) to one `Hwf : seg_wf ia 1168` -- and that
is the same fact the faithfulness obligations already need, so a chain now
threads exactly one. For scale: `ZZMladTail.linkFN` threads two (`Hrep`, `Hb`)
and every further link would add more.

TRAP: do not reach for `seg_wf_Z` here. By the time the goal is reduced the
byte count is a Z LITERAL, so `apply seg_wf_Z` must unify `Z.of_N ?b` with
`20` -- inverting `Z.of_N`, which unification will not do. `seg_bound` instead
uses `seg_wf_bin` at bound 0 purely for the no-truncation fact and finishes
with plain `lia`.

**What still needs manual work at a cut, in order of cost:**

1. **A register whose VALUE changes across the cut.** The generator makes both
   sides the same term; here they genuinely differ (`dv_step_at`'s T4: post says
   `T4 |-> dvdec (term_var "k")`, the next pre says `T4 |-> term_var "k"`).
   Costs `asn_regidx_pts_inst` plus a premise that restates both terms and both
   valuations in full -- **14 of `dv_step_at`'s 43 lines**. This is now the
   single largest remaining item.
   UNTESTED IDEA: have a segment's post name a FRESH Sigma variable and a pure
   equation (`asn.exist "k2" (T4 |-> term_var "k2" ∗ formula (k2 = dvdec k))`)
   instead of a computed term, so the spatial part frames and the arithmetic
   becomes a pure side goal. Risks: an existential in a postcondition may cost
   VC time, and the composition has to instantiate the witness. MEASURE IT.
2. **The per-segment valuations** (`mI`, `nI`). Mechanical, hand-written, and
   they grow with |Sigma| -- which 3g just enlarged by moving cell values into
   it. Derivable from the cut spec in principle; untested.
3. **iProp-level existential quantification of the cell values.** Four cells is
   `∃ v0 v1 v2 v3`; sixteen is worse, and every step lemma introduces and
   repackages them. `dvInvN` shows the pattern for one variable. A combinator
   quantifying a whole Sigma-suffix would do it; untested.
4. **Fuel.** Still hand-tuned per segment, still no evidence for a formula.
5. **Reuse at a different address.** A re-based contract no longer mentions the
   program base, but it still names `iq` concretely in `cfg_init_addr` and
   `cfg_exitCond`, because `seg_exitCond` is a concrete `bv -> bool`.
   Verify-once-reuse-anywhere needs that quantified too.
6. **The invariant itself** -- which is the specification, and should stay
   hand-written.

### 3i. LOOPS ARE ALLOWED TO BE DIFFERENT (2026-09-11)

The owner's observation, and it holds up: the one thing the cut generator cannot
collapse -- a register whose VALUE changes across the cut (`dvdec`) -- is
specific to LOOP BACK EDGES, not to cuts in general. The reason is structural,
not incidental:

- At a **straight-line cut** you CHOOSE the cut assertion, so you can always
  describe the state with fresh Σ variables and no computed terms. `cut_MN` is
  the demonstration: pure data, one `iFrame`.
- At a **back edge** you cannot. The invariant must be the SAME assertion at
  entry and exit, and something must decrease, so the relation between the two
  states is forced into the open. `dvdec` IS that relation
  (`T4 |-> dvdec k` in the post vs `T4 |-> k` one trip on).

So the right split is: cuts are data; loops carry one extra piece of
arithmetic, and that is the price of a back edge.

**`dvdec`, for the record.** `dvdec t := t +b 0xFFFFFFFF` in `ZZMladDvGen.v` --
`t - 1` in 32-bit two's complement. It is index 135 / byte 540, the loop head,
`addi T4, T4, -1`. It is written as an ADD and not `bop.bvsub` (which exists)
because that is what the executor produces: `Machine.v:1200` gives
`RISCV_ADDI => rs1_val +b immext`, RISC-V sign-extending the 12-bit `-1` to
`0xFFFFFFFF`. MEASURED: rewriting `dvdec` as `term_binop bop.bvsub t 1` -- same
value -- makes `solve_seg` fail with `No applicable tactic`. **The spelling is
load-bearing; mirror the executor's term, do not simplify it.**

**Landed: `myWP2_loop_mono`** (`GenCompose.v` §4, 2 lines). Corrects the
retraction above. `dv_step_at` now states what a trip does --
`dvInvAt ia F (m+1) -∗ myWP2_loop (dvInvAt ia F m)` -- instead of being
parameterised over an arbitrary continuation, and the weakening moves to the
call site (`iApply (myWP2_loop_mono _ _ (dvInvAt_to_N …))`).

**BUT the line saving is 2, not the ~27 I estimated.** `ZZMladDvLoop2.v`
204 -> 202 code lines. `dvInvAt_to_N` / `dv_step` / `dv_exit` are still needed:
they bridge the kv-indexed invariant to the trip-indexed one, which is
indexing, not weakening, and mono does not touch it. The value of mono is that
the per-trip lemma is now a standalone, reusable statement -- not brevity.
Do not quote the 27.

### 3j. THE BLUEPRINT, AND WHAT IS STILL MISSING FROM IT (2026-09-11)

Asked: is there a blueprint for cuts and loop invariants needing essentially
zero manual effort beyond identifying the invariant? **For cuts, yes and it is
demonstrated. For loops, the pieces exist but nothing has been assembled
end-to-end, and the per-trip lemma is still ~38 hand-written lines.**

DEMONSTRATED:

| step | what you write | status |
|---|---|---|
| segment contract | `gen_seg_contract …` | 1 line + `Proof. solve_seg. Qed.` |
| its VC | `solve_seg` | 1 line |
| sub-table + exit faithfulness | `eq_refl eq_refl Hwf`, inline | 0 lines |
| every address-space bound | one `seg_wf ia bound` for the whole chain | 0 per cut |
| a STRAIGHT-LINE cut | `solve_cut cpost cpre` | **1 line** |
| a loop | `seg_loop` + `myWP2_loop_mono` | combinators done |
| a value change at a back edge | fresh Σ var + pure equation in the post | see below |

**NEW THIS ROUND, and it is the one that mattered.** The `dvdec` problem is
solved by construction, not by a lemma. Write the post as

```coq
asn.exist "k2" ty_xlenbits
  ( T4 |-> term_var "k2"
    ∗ asn.formula (formula_relop bop.eq (term_var "k2") (dvdec (term_var "k")))
    ∗ asn.formula (formula_secLeak (term_var "k2")) )
```

instead of putting the computed term `dvdec k` in the spatial part. MEASURED:
the VC still discharges (`solve_seg`, 21.7 s), the `asn_regidx_pts_inst` rewrite
and BOTH written-out valuations disappear, and the arithmetic becomes
`destruct v; cbn in Heq; subst w; rewrite dv_dec`. `ZZMladDvLoop2.v` 202 -> 196
code lines, and **`asn_regidx_pts_inst` is now referenced by no call site**
(kept as the fallback). The rule: **a cut assertion, at a back edge too, must
be DATA -- never a computed term.**

STILL MISSING, and a blueprint claim should not be made until these close:

1. **The per-trip lemma body is 38 lines** (`dv_step_at`), `dv_exit_at` another
   22. Roughly: HPre ~18 (of which the latch guard is real program content and
   the rest is `iSplit`/`iFrame`/`cbn` scaffolding), HPost ~12. A `solve_step`
   tactic on the model of `solve_cut` looks feasible -- NOT built, NOT tested.
2. **Invariant PACKAGING, ~28 lines** (`dvI`, `dvInvAt`, `dvInvN`, `dvOut`).
   Identifying the invariant is the user's job and should stay so; the
   valuation, the `∃kv`/`kv = n+2` trip bridge and the exit state are
   boilerplate on top of it and look derivable.
3. **THE TWO LINES OF WORK HAVE NEVER BEEN COMBINED.** `ZZRebaseN`/`ZZRebaseCut`
   (re-based contracts, generated cut assertions) and `ZZMladDvLoop2` (the loop)
   are separate probes; the loop still uses the OLD shared-base style with
   hand-written cut assertions. Until one program uses both, "blueprint" is a
   projection, not a result.
4. **No re-based GENERATOR exists.** `sgN_reb` was hand-written as a record
   literal; `gen_seg_contract` still takes `ia`/`head`.
5. Fuel is still hand-tuned. Reuse at another address still blocked by
   `cfg_init_addr`/`cfg_exitCond` naming `iq` concretely.

### 3k. A FOR-LOOP TACTIC: possible, but NOT over a free-form invariant (2026-09-11)

Asked whether a tactic specialised to counted for-loops (which is what compiled
C gives us) could absorb the per-trip lemma the way `solve_cut` absorbs a cut.
Most of `dv_step_at`'s 38 lines ARE generic -- the two `iIntros` patterns, the
split-before-framing dance, `rewrite seg_addr_add`, the final bound. What is
per-loop is the guard at trip m and the decrement arithmetic, and for a counted
loop both are small.

The blocker is the `iDestruct` pattern, and it is not cosmetic. MEASURED, three
ways on the same goal:

| how the invariant hypothesis is broken up | `iFrame` |
|---|---|
| named, arity-aware: `iDestruct "H" as "(Hbnd & HT4 & Hsl & Hregs & Hmin)"` then `iFrame "Hbnd HT4 Hsl Hregs Hmin"` | **0.35 s** |
| arity-blind `repeat (iDestruct "H" as "[? H]")` then bare `iFrame` | **TIMEOUT > 300 s** |
| same, with `minimal_pre` also unfolded so both sides split alike | **TIMEOUT > 150 s** |

So the named pattern is doing two jobs, and the second one is invisible: it
says WHERE TO STOP SPLITTING (at `minimal_pre`, keeping it whole), and it gives
`iFrame` an explicit ORDERED list. Bare `iFrame` over many separate hypotheses
explodes -- the same pathology already recorded for the opposite extreme
(`iFrame "Hpc"` alone, one hypothesis at a time, also > 300 s). **iFrame wants
a named list of the right length; both "all at once, unnamed" and "one at a
time" are pathological.**

Consequence, and it is the same conclusion as everywhere else in this file:
**a per-trip tactic is writable only against a GENERATED invariant**, whose
conjunct structure -- hence the destructure pattern and the frame list -- is
fixed and known. Against a hand-written invariant the pattern is part of the
specification and cannot be inferred.

So the shape of the thing to build is `gen_loop_inv base regs mems counter`
(fixed arity) plus `solve_loop_step`, leaving exactly two obligations per loop:
the guard holds at trip m, and the counter decrements. For a compiled C
for-loop those are one `lia` and one `dv_dec`.

NOT BUILT. It collides with the `LoopSpec` decision in §4 -- which was taken
against a record that CONSTRUCTS the invariant, because the two worked loops
differ exactly there (G has a fixed footprint and uses an opaque frame; the
tail slides and uses a cell-range fixpoint). `gen_loop_inv` would have to
handle both, or be restricted to the fixed-footprint case and say so. That
fork needs deciding before it is written, not after. (Note §4's memory-builder
objection is partly overtaken: `gen_mem_at`, values-as-parameters, now exists.)

### 3l. THE PER-TRIP TACTICS -- and a correction to 3k (2026-09-11)

§3k concluded that an arity-blind per-trip tactic was impossible because
`repeat (iDestruct … as "[? H]")` + `iFrame` timed out. **That diagnosis was
wrong, and the correction is the whole reason the tactics exist.** The blow-up
was not the over-splitting, it was the BARE `iFrame`. Measured on one goal:

| hypothesis handling | `iFrame` |
|---|---|
| named, correct arity: `"(H1 & … & H5)"` + `iFrame "H1 … H5"` | 0.35 s |
| named, DELIBERATELY OVER-SPLIT (6 parts) + `iFrame "H1 … H6"` | **1.98 s** |
| arity-blind peel, each framed BY NAME: `repeat (iDestruct "H" as "[Hx H]"; iFrame "Hx")` | **2.1 s** |
| arity-blind peel + BARE `iFrame` | timeout > 300 s |
| same, both sides split alike + bare `iFrame` | timeout > 150 s |

So `iFrame` is fine with any splitting as long as it is given an explicit NAMED
target; it is bare `iFrame` over many hypotheses that explodes. Peel one, frame
it by name, repeat -- and the tactic needs to know no arity at all.

**LANDED** (`GenCompose.v`, after `End SegCompose`):

```coq
Ltac solve_step_pre  c win instrRes      (* leaves: the loop GUARD *)
Ltac solve_step_post c inv win instrRes  (* leaves: the counter DECREMENT *)
```

`solve_step_pre` is fully arity-blind. `solve_step_post` matches the post's
top-level shape `(counter-block ∗ rest) ∗ minimal_pre`, which is what the
blueprint prescribes (§3j), so it is matching a generated shape rather than
guessing; `rest` is peeled blind. It leaves `v`, `Heq` and `Hc` in scope for the
caller's arithmetic -- **Ltac1 resolves a hypothesis name at DEFINITION time, so
a tactic cannot itself say `cbn in Heq` for a name its own `iDestruct`
introduces**; the caller does it, where the name exists.

`dv_step_at`: **38 -> 24 code lines**, and what is left is exactly (a) the
`seg_step1` argument block, (b) the latch guard, (c) the decrement. File
196 -> 182. Gate PASSED 5m56s, 18 theorems axiom-clean.

`seg_bound` gained a second case: the goal is sometimes `bv.bin (of_N ia)` with
no shift, and `cbn` reduces `Z.of_N 1168` to the literal `1168` so `seg_wf_Z`
cannot apply (the `Z.of_N` inversion trap again, §3h).

NOT DONE: `dv_exit_at` (22 lines) still uses the long form -- its post has no
counter block, so `solve_step_post`'s prescribed shape does not fit it. An exit
segment wants its own, simpler tactic. And the `seg_step1` argument block (6 of
the 24 lines) still wants the `SegSpec` record from §3e.

### 3m. WHERE THE MEMORY STARTS (2026-09-11)

It is already a free parameter, and deliberately so. `loopCtx` carries TWO
bases: `"q"`, the loop's own code base, and `"d"`, the data base. The generated
contract says exactly one thing about `"d"` --

    unsigned (term_var "d") + ls_dbound <= lenAddr

-- an address-space bound. **Nothing relates `d` to `q`.** Where the data
starts is not decided in the contract at all; composition supplies it, exactly
as it supplies `q`. For muladd that will be `q = programBase + 540` and
`d = programBase + 1128`, and the loop contract sees neither.

MEASURED 2026-09-11: putting a cell at `d + 0` into `ls_mem_a`/`ls_mem_an`
elaborates at both contexts and `solve_seg` still discharges (1.60 s vs
1.51 s without). CAVEAT: divrem never READS that cell, so this validates the
plumbing -- the cell rides in the frame across the loop -- and NOT a load
through `d`. The first loop that actually reads memory is still the real test.

Three limits worth knowing before relying on it:

1. **One data base, one contiguous span.** `ls_dbound` bounds a single region
   from `d`. A loop touching two disjoint regions (an input array and an
   output array at unrelated addresses) needs two bases; today the second one
   has to be folded into `ls_mem_a` with its bound stated by hand. Extending
   `loopCtx` to a fixed small number of data bases is easy; making the number
   arbitrary re-opens the weakening problem that fixing the context solved.
2. **No disjointness is generated.** Not between the data region and the code,
   and not between cells. Code-vs-data does not need it in this model
   (instructions live in a separate `ptsto_instrs` resource, so a data write
   cannot corrupt them). Cell-vs-cell DOES matter for a sliding loop -- that
   is what `seg_addr_neq` is for, and the LoopSpec does not emit it.
3. `ls_mem_a` / `ls_mem_an` are two hand-written copies, one per context,
   because a cell's value sits under `asn.exist "mv"` while its address
   mentions the base.

### 3n. THE OTHER SIX MULADD LOOPS DO NOT FIT (2026-09-11)

Asked to re-verify muladd's remaining loops through the LoopSpec with no hand
work. **They do not fit**, and the blocker is a decision I made while
implementing, not something inherent.

Scanning `mlad_instrs` for backward branches finds SEVEN loops:

| head idx / byte | body | branch | fits? |
|---|---|---|---|
| 16 / 64 | 25 | `bltu A5, A4` | limit is a REGISTER |
| 84 / 336 | 6 | `bnez T6` | counter OK, but memory SLIDES |
| 113 / 452 | 5 | `bne T3, T0` | no counter; pointer vs register; slides |
| **135 / 540** | **27** | `bltu T5, T4` | **divrem -- VERIFIED** |
| 190 / 760 | 29 | `bne A1, T1` | pointer vs register; slides |
| 237 / 948 | 13 | `bne T5, S0` | two pointers; slides |
| 264 / 1056 | 13 | `bne A4, A2` | pointer vs register; slides (the tail) |

DEMONSTRATED, not predicted: `Example/ZZLoopBProbe.v` states loop B -- the
closest fit, since T6 is a genuine counter decremented to zero -- and
`solve_seg` fails. The residual ends in `Erasure.eerror` immediately after the
guard is assumed: the first instruction `lw S1, -4(S0)` has no `ptstomem`
chunk to read, because with `ls_regs` a CONSTANT the strongest thing the spec
can say about the walking pointer S0 is "some secret value".

TWO GAPS, both mine:

1. **`ls_regs` / `ls_mem_a` are constants.** The design proposed
   `nat -> list reg_spec_rel`; the implementation made them constants. BUT
   trip-indexing is NOT the right fix, and it is worth being clear about why:
   a contract is verified ONCE and used at every trip, so it cannot depend on
   `n`. The moving pointer has to be a LOGIC VARIABLE in the context, with the
   cells addressed off it and the INVARIANT instantiating it per trip -- which
   is exactly what the hand-written sliding loops already do (`amCtx` carries
   `ap`, `bp`, `e`).
2. **`loopCtx` is fixed at `["q"; "d"; "k"]`.** Six of the seven loops compare
   against a REGISTER, which needs a limit variable, and every one of them
   walks a pointer, which needs a pointer variable. There is no room.

So the fixed context -- the simplification that made this tractable at all
(§4: no double-passing of terms, no weakening under `asn.exist`) -- is
precisely what stops it generalising. That is the trade, stated plainly.

THE FIX, and it is bounded: make the context a PARAMETER,
`ls_ctx : LCtx`, with the counter, the bases and the pointers as terms over
it. The record then gains a few fields duplicated at two contexts, exactly as
`gen_seg_contract` already has `base`/`base_a`. It does NOT re-open the memory
weakening wall, because `ls_mem_a`/`ls_mem_an` are already per-context
assertions supplied by the caller.

VERDICT on "can loop verification be done without too much boilerplate now":
for a counted loop with a FIXED footprint, yes -- divrem is two `solve_seg`
one-liners off a 17-field record. For muladd's other six, no, and it needs the
context parameterised first.

### 3o. THE FIX APPLIED: Sigma-parametric LoopSpec (2026-09-11)

`LoopSpec` is now `Record LoopSpec {Σ : LCtx}`. The code base and the counter
are explicit TERMS, supplied once per context they appear in; the bases are a
LIST of (term, bound) pairs whose address-space conjuncts are generated; and
`ls_extra_a`/`ls_extra_an` is the escape hatch for what a spec list cannot
say -- a walking pointer's value, memory cells, an extra bound.

The counter needs FOUR copies (`ls_k_a`, `ls_k_an`, `ls_k_anc`) because the
post binds a fresh variable and a `Term (Σ ▻ "a" ▻ "an")` does not weaken under
`asn.exist "c"`. Writing `term_var "k"` four times is tedious, but it is
resolution, not proof.

RESULTS:

- **divrem still verifies**, 1.36 s (was 1.51 s) -- and its context SHRANK to
  `["q"; "k"]`. The fixed version forced an unused data base into every loop;
  now a loop declares exactly the variables it has.
- **loop B now verifies** -- idx 84..89, the memmove-down loop, which the
  fixed-context version could not even STATE. Its walking pointer S0 is a
  logic variable `"sp"`, the two cells it touches are addressed off it, and
  the guard is `c <> 0` against the counter T6.

So muladd is 2 of 7 loops through the framework, against 1 before, and the
five remaining are now EXPRESSIBLE -- the guard may mention any variable in
Σ (so `bne T3, T0` against a register limit is fine) and a pointer may be a
variable (so a sliding footprint is fine). What is left for them is
spec-writing, not a framework limit.

ONE NEW GAP, and it is small and precise. Loop B's `solve_seg` gets the
executor ALL THE WAY THROUGH the body and leaves exactly ONE residual: the
upper bound for the access at `sp - 4`. `solve_symbase_fetch` cannot close it
because it only knows base PLUS a positive offset, and this address is
`0xfffffffc + sp`, whose `bv.bin` WRAPS. Discharged by hand in the probe:

    rewrite bv.bin_add; (bv.bin of the literal and bv.exp2 32 by vm_compute);
    replace (c + bin w) with ((bin w - 4) + 1 * 2^32) by lia;
    rewrite N.Div0.mod_add; apply N.mod_small; lia.

The right fix is a `fetch_bound_step_neg` beside the existing
`fetch_bound_step`, so `solve_symbase_fetch` handles base-minus-offset. Until
then, any loop walking a pointer DOWNWARD pays ~10 lines once.

(Two syntax notes banked: `rewrite H1, H2.` and `rewrite ... by tac` both hit
`Syntax error: [ltac_use_default] expected` through rocq-mcp; split into
separate `rewrite` calls and a braced sub-proof.)

### 3p. fetch_bound_step_neg: lemma DONE, tactic wiring NOT (2026-09-11)

`Contracts.relval_fetch_upper_neg` is proved and landed: the upper fetch/access
bound for an address BELOW the base, `cbv + v` with `cbv` the two's-complement
encoding of `-D`, where `bv.bin` WRAPS so
`relval_fetch_upper_add`'s no-overflow step does not apply. Premises are the
base's upper bound, its LOWER bound (`D <= unsigned v` -- a contract must
supply it, or the access really does underflow), the encoding
`Z.of_N (bin cbv) + D = Z.of_N (exp2 xlenbits)`, and `A <= B + D`.

TWO TRAPS BANKED:
- **`D` must be a plain `Z`, not `Z.of_N D`.** The goal's offset arrives as a Z
  LITERAL, so `eassumption` would have to unify `Z.of_N ?D` with `4` -- the
  `Z.of_N` inversion trap, same as `seg_wf_Z` in §3h. Stating D : Z fixed it.
- **`replace S with (S - E + 1 * E) by lia` fires inside its own RHS.** The
  resulting goal is unprovable-looking (`S-E+1*E-E` vs `S-E`). `set` both atoms
  first and restrict with `at 1`.

NOT DONE: the `solve_symbase_fetch` alternative does not fire end to end.
`eapply relval_fetch_upper_neg` DOES apply and produces the five subgoals, and
`eassumption` closes the first individually -- but the bulleted chain inside
`solve [...]` fails. Prime suspect: `eapply` leaves 2 SHELVED goals, and
`solve` counts shelved goals as unfinished. Next thing to try is
`unshelve eapply` or an `Unshelve` tail, mirroring however
`relval_fetch_upper_add` gets away with it.

So loop B still carries the ~10-line hand arithmetic; the lemma that should
replace it exists and is proved, and only the plumbing is missing.

### 3q. LOOP C FITS -- the generality check passes (2026-09-11)

Loop C (idx 113..117) was chosen precisely because it violates BOTH assumptions
the counter fields appear to make:

    113  lw   T2, -4(T1)      114  addi T3, T1, -4     115  sw   T2, 0(T1)
    116  mv   T1, T3          117  bne  T3, T0

There is NO counter register -- the loop variable IS the pointer T1 -- and the
limit is another REGISTER, T0, not a constant. It fits anyway, for three
reasons worth naming because none was designed in:

1. **The "counter" may be the pointer.** `ls_imm := -4`, and the guard is
   applied to `ls_step`, which is exactly the value `bne` tests (`T3 = T1-4`).
   The decrement-then-test convention happens to be what a pointer loop does
   too.
2. **`ls_guard` may mention ANY variable of the context**, so a register limit
   is just a logic variable `"e"` that T0 is pinned to. This is the thing the
   FIXED context could not do (§3n).
3. **`ls_at` is not consulted by the contracts at all.** So a counter whose
   value is SYMBOLIC -- here `e + 4n`, not a concrete address -- costs
   nothing. NOTE: `ls_at` is currently a DEAD FIELD; `loop_inv` takes the
   valuation family from the caller. It will earn its place when the loop
   theorem's induction is written, and not before.

RESULT: `solve_seg` drives the executor through the WHOLE body and leaves
exactly ONE residual, IDENTICAL in shape to loop B's -- the `base - 4` access
bound -- closed by the same ~10 lines. Non-vacuity checked: delete the
`4 <= unsigned p1` conjunct and the arithmetic step fails, i.e. the contract
genuinely needs the lower bound it supplies.

muladd is now **3 of 7 loops** through the framework (divrem, B, C), and the
two remaining shapes are the counter-vs-counter `bltu A5, A4` at idx 16 and the
two-pointer loops at 190/237/264. Nothing seen so far suggests they do not
fit; what they need is spec-writing.

### 3r. ALL SEVEN MULADD LOOPS VERIFY (2026-09-11)

Every backward branch in `mlad_instrs` now has a LoopSpec whose body contract
discharges. Probes are `Example/ZZLoop{A,B,C,D,F,Tail}Probe.v` and
`ZZDvLoopSpec.v`.

| head idx / byte | instrs | branch | shape | proof |
|---|---|---|---|---|
| 16 / 64 | 25 | `bltu A5, A4` | counter, no memory | `solve_seg`, 1.02 s |
| 84 / 336 | 6 | `bnez T6` | counter + pointer walking DOWN | `solve_seg` + ~10 lines |
| 113 / 452 | 5 | `bne T3, T0` | pointer IS the counter, walks DOWN, register limit | `solve_seg` + ~10 lines |
| 135 / 540 | 27 | `bltu T5, T4` | counter, no memory (divrem) | `solve_seg`, 1.36 s |
| 190 / 760 | 29 | `bne A1, T1` | two pointers UP, register limit, MUL/MULHU/SLTU | `solve_seg`, 2.09 s |
| 237 / 948 | 13 | `bne T5, S0` | two pointers UP, register limit | `solve_seg`, 0.76 s |
| 264 / 1056 | 13 | `bne A4, A2` | two pointers UP, register limit (the tail) | `solve_seg`, 0.65 s |

**Five of seven are a bare `solve_seg`.** The two that are not are exactly the
two that walk a pointer DOWNWARD, and what they pay is the `base - 4` access
bound that `relval_fetch_upper_neg` exists to absorb once its
`solve_symbase_fetch` wiring is finished (§3p). Nothing else needed hand work.

THE RECIPE, which is now uniform:
- whichever pointer or counter the BRANCH tests becomes `ls_ctr` / `ls_k_*`,
  with `ls_imm` its per-trip update;
- every OTHER moving pointer goes in `ls_extra_a` / `ls_extra_an` with its
  entry and exit value;
- the limit, if a register, is a logic variable the guard mentions;
- cells go in `ls_extra_*`, bases and their bounds in `ls_bases_*`.

TWO FINDINGS WORTH KEEPING:

1. **Loop D's `sltu T4, A6, T4` (idx 194) does NOT hit the documented
   secret-data comparison wall.** `cfgver-solve-vc` records that SLTU on
   private operands leaves an unclosable `secLeak ?v` goal. Here it does not,
   because the comparison's result feeds only branchless arithmetic (idx 195
   `add T3, T3, T4`) and is never branched on nor leaked. The wall is about a
   comparison whose result must be PUBLIC, not about SLTU per se.
2. **The non-aliasing conjunct is REDUNDANT.** The tail loop verifies with
   `ap <> bp` REMOVED: separating conjunction already forces the two
   `ptstomem` chunks apart, so a contract owning both cells cannot have them
   alias. `seg_addr_neq` is for a SLIDING invariant that must show successive
   cells distinct -- not for a single trip's footprint.

NON-VACUITY spot-checked per shape, not assumed: divrem (unpin T5 -> fails),
loop C (drop the lower bound -> fails), loop D (drop the second memory cell ->
`No applicable tactic`).

STILL TRUE: this is the one-pass BODY contract for each loop. The loop
THEOREM -- HPost, the exit lemma, the induction -- is unfinished (§3o), so
"verifies" here means every loop's body contract discharges, not that any loop
is proved to run to its exit.

### 3s. THE LOOP THEOREM (2026-09-11) -- generic part DONE

`GenCompose.v` §6 now carries the three lemmas, all compiling:

- **`loop_step`** -- one trip. `apply (seg_step1 …)` works generically off the
  LoopSpec, and both bullets collapse: HPre because the invariant IS the
  precondition minus the branch decision at the SAME valuation (one `iFrame`
  takes it whole, leaving only the pc equation and the guard); HPost because
  the ambient half frames and the rest is the caller's transfer.
- **`loop_exit`** -- the same with the exit guard and the fall-through target.
- **`loop_counted`** -- `seg_loop` instantiated.

What the caller supplies is exactly the loop's own content: `Hpl`/`Hpa` (the
valuation pins the code base -- `reflexivity` in practice), `Hg` (the guard
holds at trip S n), and `Htrans` (one trip's postcondition establishes the next
trip's invariant).

**`loop_inv` gained a pure side condition `P : nat -> Prop`, and it is NOT
decoration.** A counter's no-wrap bound (`ls_at n + 1 < 2^32`) holds only below
2^32, while `seg_loop`'s step is quantified over ALL n -- with nowhere to put
it the step is simply unprovable. The hand-written `dvInvN` carried exactly
this. The caller also supplies `P (S n) -> P n`, immediate for a bound that
shrinks with the counter.

TRAP, and it shaped the proof: **the two bullets of `seg_step1` are separate
goals, so an `iIntros` inside HPre does not scope over HPost** -- and HPost is
where `P n` must be re-established. Peel the pure conjunct BEFORE applying:
`unfold loop_inv at 1; iIntros "(%HP & H)"; iApply (seg_step1 … with "H")`.

END-TO-END on divrem (`Example/ZZDvLoopThm.v`): `dvI` (the valuation family),
`dvP` + `dvP_mono` (the no-wrap bound), `dv_dec` (the bitvector decrement) and
**`dv_trans` -- the trip-to-trip transfer, PROVED**. It is 12 lines: destructure
the post's fresh-variable block, show the witness equals k-1, and frame. The
bounds and the register block cross the valuation change untouched.

NOT DONE: the guard lemma (`dvP (S n) -> 1 <u k-1`, a `lia` plus two
`bv.bin_of_N_small`) and the three applications that assemble
`loop_step`/`loop_exit`/`loop_counted` for divrem -- perhaps 30 lines,
mechanical, but not written, so there is no `dv_loop` theorem yet.

### 3t. DIVREM'S LOOP THEOREM IS DONE -- and where the lines actually go (2026-09-11)

`Example/ZZDvLoopThm.v` compiles: **`dvs_loop : forall n, dvInv n -∗
myWP2_loop Post`**. The loop, not just its body contract.

Asked why the assembly was "~30 mechanical lines", I measured instead of
estimating. It is 102 code lines, and the split is not what I said:

| block | lines | what it is |
|---|---|---|
| `dvI`, `dvP`, `dvP_mono` | 6 | the valuation family and the no-wrap bound |
| `dv_dec` | 11 | the bitvector decrement -- GENERIC across counted loops |
| `dv_trans` | 19 | the trip-to-trip transfer |
| `dv_guard` | 12 | the latch holds while trips remain |
| `dv_exitg` | 8 | the latch falls through at trip 0 |
| the assembly | 46 | three `exact`s and their statements |

So the answer to "why 30 lines": it was not 30, and it is not proof. The three
assembly lemmas have **3-line proofs and 9-line statements**, and the
statements are almost entirely re-spelling `loop_inv`'s six arguments, twice
each. A one-line abbreviation

    Definition dvInv : nat -> iProp Σ := loop_inv (dvSpec iq) (dvI iq) … dvP.

removes most of it; the rest is a Section carrying `iq/pia/pbound/Fr` and four
placement hypotheses, which is the SAME unbuilt "bundle the placement facts"
abstraction §3e identified for `seg_step1` and I have now deferred twice.

`dv_dec` is generic and HAS MOVED (2026-09-12) to `GenSegment` as
`bv_of_N_wrap_dec s m : bv.add (of_N (m+s)) (of_N (exp2 xlenbits - s)) = of_N m`
-- the wrap-around add that `addi ctr,ctr,-s` compiles to, unconditional in `m`
(the no-overflow bound a loop carries is for its GUARD, not for this step).
Every counted loop's decrement is now one line
(`exact (bv_of_N_wrap_dec 1 m ltac:(bv_bound))`), 11 of the 102 gone.

Genuinely per-loop and irreducible: `dv_guard`, `dv_exitg`, `dv_trans` and the
valuation family -- 45 lines, and they ARE the loop's content.

NOT A TRAP -- RETRACTED 2026-09-12. An earlier draft of this section claimed
that passing `HP0` as an inline `ltac:(unfold dvP; bv_bound)` argument inside
the `exact` term sent coqc into a >10000 s hang, and told you to use
`assert (HP0 : dvP 0) by (…)` instead. **That is wrong.** The wall-clock came
from the laptop being suspended mid-compile, not from the term. Measured
directly (`rocq_start` at `dvs_exit`, `rocq_check` with the inline form and a
trailing `Qed.`): **35 ms**, `dvs_exit is defined`. Both forms are fine; the
`assert` in `ZZDvLoopThm.v` is kept only because it reads better.

The method lesson that survives, and the reason this took a measurement to
settle rather than a glance: **a wall-clock number from an unattended compile is
not evidence of anything.** Suspend, swap and a contended machine are all
invisible in "the call returned after N seconds". Before attributing a hang to a
term, reproduce it interactively -- here that cost one `rocq_start` plus one
`rocq_check`. (Include the trailing `Qed.` in the body: without it the kernel
check never runs, so a `rocq_check` can go green on a body that `coqc` would
reject.)

## 4. Deliberately NOT built

- **No memory-block builder.** A Σ-generic one needs the base weakened under
  the `asn.exist "mv"` binder, and the only weakening to hand is
  `subst _ sub_wk1` (a recorded Θ(|Σ|²) driver, and non-transparent for
  `iFrame`). More to the point, **neither worked precedent needs it**: G
  touches no memory, and the sliding window of the `br_i31_sub` loop has
  addresses that are logic variables, not base-plus-literal, so it states its
  cells in `extra_pre`. Generalising from zero examples is how the previous
  round went wrong. Add it when a segment with a fixed base-relative memory
  block actually appears.
- **No `LoopSpec` record → one theorem.** The two worked loops differ exactly
  where such a record would have to be uniform: G uses an opaque frame (fixed
  footprint), the tail uses a `cellsPriv`/`cellsPub` fixpoint (sliding
  footprint). `seg_step` + `seg_loop` sit below that fork.

**The rule of thumb this yields:** opaque frame when a loop's footprint is
FIXED, cell-range fixpoint when it SLIDES.

---

## 5. Traps banked while building this

- **`Set Implicit Arguments` leaks.** `GenContract.v` sets it non-`Local`, so
  it reaches every consumer. It silently made `seg_step`'s `iota` implicit —
  and since **only implicit arguments can be passed by name**, the explicit
  ones then had to be positional. Both new files do `Local Unset Implicit
  Arguments`; implicit marks are baked in at definition time, so consumers see
  predictable signatures regardless. (This is the same flag that makes
  `itable_faith_of_segment`'s pre/seg/post unnameable — ZZMladTail.v's header
  records it.)
- **`cfg_map` is STUCK on an abstract record**, so a combinator cannot consume
  `ValidCFGVerifierContract c` for a variable `c`. `seg_vc` unblocks it:
  `destruct c; exact (fun H => H)`.
- **`%N` does not beat `exp_scope`.** `(4 * N.of_nat m = off)%N` elaborates `4`
  as a `Term`. Write `@eq N (N.mul 4 (N.of_nat m)) off`. (Already in
  rocq-pitfalls; hit again.)
- **`rewrite … by …` does not parse inside a bullet** — sequence it instead.
- **A rebuilt `.vo` is invisible to a live pet session.** Adding `S0..S3` to
  `Tables.v` produced `The reference S3 was not found`, with a `.vo` newer than
  the source. `force_restart=True`.
- `exact` unifies up to conversion where `rewrite` does not, which is why
  `itable_faith_at`'s `off` can be given as `540` and matched against
  `4 * N.of_nat 135`.

---

### Traps added by the port (2026-09-10)

- **A polling predicate that matches the tool's own banner.** Waiting on
  `scripts/gate.sh` with `grep -q "GATE" <log>` matches its hint lines
  (`override with GATE_JOBS=N`), so every poll returned at once and I concluded
  the gate had stalled for hours and killed two runs. It had not: with a correct
  end-marker (`^real`) it passes in **5m50s**. Key on a token that can only
  appear at the END. Same self-match class as the four hook misfires CLAUDE.md
  banks. What IS measured about gate memory: an `AxiomProbe` peaks at ~7 GB
  regardless of `GATE_PROBE_BATCH`, because the cost is loading `Results.vo`'s
  closure — so RAISE the batch (fewer loads), never lower it.

- **`rewrite ?lemma in *` can fail with "assumptions should be named
  explicitly."** I "improved" `bv_bound` from `change … ; lia` to
  `rewrite ?exp2_xlenbits in *; lia` and broke it. The message names no
  hypothesis and points at the `assert`'s binder, so it reads as a parse error
  in your own tactic. `pose proof exp2_xlenbits; lia` does the same job (hand
  lia the equation and let it treat `bv.exp2 xlenbits` as an atom) and works
  whether the bound arrives in the goal or in a hypothesis.
- **`iApply HP` re-folds the goal**, so any `unfold` done before it is thrown
  away. Apply the continuation first, then unfold.
- **`subst kv` picks the FIRST equation on `kv`**, which is the
  `N.of_nat (S k)` form the invariant exists to avoid. `clear Hkv.` before
  `subst`.
- **`N.le` `vm_compute`s to `Lt <> Gt`, which `lia` cannot close** —
  `discriminate` does. The `nat`-`le` sibling in the same proof is a real
  inequality and does want `lia`, so the two bullets of one `itable_faith_at`
  application need different tactics.

## 6. Open

- **The other cuts.** Nine straight-line segments and three sliding loops still
  need real postconditions and cut assertions. The machinery is now
  call-site-tested, but only on a FIXED-footprint loop; the three sliding loops
  need the cell-range fixpoint, which is untouched by this work.
- **Gate coverage.** `GenCompose.vo` is listed explicitly in `gate.sh`'s
  `BUILD_TARGETS` because nothing in `Results.vo`'s closure Requires it yet.
  Drop it from that list once a tracked `Example/*Result.v` depends on it.
- **A dedicated skill.** `skill-path-guard.sh` currently maps the two new files
  onto existing skills. Per CLAUDE.md a new skill must be authored through
  `skill-creator`, not hand-written; that is the right follow-up rather than a
  hand-rolled `SKILL.md`.

## 3u. The per-trip obligations become LEMMAS (2026-09-12)

Asked whether the per-loop ritual wanted a tactic or a lemma, and told lemmas
(the `cfg_instrs_endToEnd` precedent: one general lemma, side conditions at the
call site). It wanted lemmas, and the survey of the seven loops says why the
ritual looked tactic-shaped in the first place: the obligations could not be
STATED generically, because the valuation family is hand-written and nothing in
`LoopSpec` relates trip `n+1` to trip `n`.

Landed (commit 750ac416):

- **`GenSegment`: `loop_latch_neq` / `_eq` / `_ult` / `_ule`.** The branch
  obligation of `loop_step` / `loop_exit`. Hypotheses are the counter's value
  off the valuation, the machine's step (`Hstep`), two `< 2^32` bounds and one
  numeric fact -- all in `N`, so a caller never touches `bv.bin`.
- **`GenCompose`: `loop_trans`.** The trip-to-trip transfer. Does the four
  generic moves (open the counter existential, refute `NonSyncVal` from
  `secLeak`, rewrite the step, frame) and leaves `Hstep` plus **`Hframe`**:
  the frame at trip `S n` implies the frame at trip `n`.

Two relop families, not one relop-parametric lemma -- the parametric version
needs guard/exit complementarity as a per-loop side condition, i.e. most of
what these exist to delete. The seven loops use exactly two families:
`neq`/`eq` against a sentinel (5 of 7; the sentinel is a variable in C/D/F/Tail
and the literal 0 in B) and `ult`/`ule` against a literal bound (divrem, A).
Strides are -1, -4 and +4; `Hstep` is `bv_of_N_wrap_dec` for a decrement and
`eq_sym (bv.of_N_add ..)` for an increment.

### Verified against all seven, and it is NOT all good news

`Example/ZZLoopLatchCheck.v` -- **14 latch obligations, all seven loops, no
admits, 21 s.** Both relop families, both stride directions, literal and
variable sentinels. The latch lemmas are general.

`Example/ZZLoopTransCheck.v` -- `loop_trans` on A (footprint does not move:
the whole transfer closes, `Hframe` is one `iFrame`) and on D (two walking
pointers: `loop_trans` applies unchanged, `Hframe` is exposed).

**And `Hframe` is NOT PROVABLE for D from `ldSpec` as written.** Read off both
sides of the goal, the trip-`S n` frame is short of the trip-`n` frame by:

1. **the cells are at the old addresses** -- `ld_extra_an` gives `p1 ↦ₘ _`,
   `p7 ↦ₘ _` at pe-4(n+2)/p7e-4(n+2); trip `n` needs pe-4(n+1)/p7e-4(n+1);
2. **`p1 ≠ p7` is dropped** -- asserted by `ld_extra_a`, absent from
   `ld_extra_an`.

This is a gap in the SPEC, not in `loop_trans`: `ls_extra_a`/`ls_extra_an` are
fixed assertions describing ONE trip's window, with no reservoir to draw the
next cell from, and `loop_inv`'s `Fr` is trip-independent too. An array loop
needs `ls_extra_*` indexed by the trip index. **The six muladd probes were
only ever checked at CONTRACT level (`solve_seg`); this is the first time
their back edges were examined, and 5 of 7 cannot close one.** divrem and A
(no memory in the frame) are the two that can.

### The line count barely moved, and that is the honest headline

divrem's per-loop block: **49 -> 45 code lines.** The 26 lines of proof became
~15 lines of argument list. What changed is the KIND of line, not the number:
every remaining line is data (a counter value, a bound, a valuation) rather
than reasoning, and every loop's lines are now the same shape. The next real
cut is a `loop_counted_ult` / `_neq` that bundles all three obligations plus
the placement facts into ONE lemma per relop family -- the `endToEnd` shape
done properly, which would take the call site to ~10 lines. Not built.

### One real trap (and it is the small true version of a retracted one)

`exact (loop_latch_ult (dvSpec iq) _ 1 .. ltac:(cbn; do 2 f_equal; lia) ..)`
fails with **"Cannot find witness"**. The `_` for the valuation leaves the
inline `ltac:`'s EXPECTED TYPE full of evars, so `lia` runs on a goal that is
not yet a goal. Writing the valuation out fixes it (85 ms). Note this is the
genuine, narrow version of the claim retracted in §3t: `ltac:` in a term
argument is fine -- `ltac:` in a term argument *behind an undetermined `_`* is
not. The `refine (.. _ _ _); bullets` style avoids the question entirely and
is what D/F/Tail use.

## 3v. All seven back edges CLOSE (2026-09-12)

§3u found that 5 of 7 loops could not close their back edge. Fixed. The cause
was one design decision, not five bugs: **`loop_inv`'s ambient frame `Fr` was
trip-INDEPENDENT**, so an array loop had nowhere to keep the cells it had not
reached yet. The body consumes the cell at the current pointer and the next
trip needs the cell at the next one, which was never anywhere in the invariant.

### The fix, in three generic pieces (commit 742b47da)

- **`Fr : nat -> iProp Σ`** in `loop_inv` / `loop_step` / `loop_exit` /
  `loop_counted`, and `loop_trans` gains `FS`/`Fn`. `Htrans` is now
  `post(S n) ∗ Fr (S n) ⊢ win(n) ∗ Fr n`, so the trip-to-trip step can EXCHANGE
  resources with the reservoir instead of only framing.
- **`loop_res A iota q n`** (GenCompose) -- the reservoir, defined as the
  loop's own cell assertion `A` interpreted at EVERY FUTURE TRIP'S VALUATION:
  `[∗ list] i ∈ seq 0 n, asn.interpret A ((iota i).[a↦q])`. This is the trick
  that avoids all binder machinery -- the cells trip `i` needs are by
  construction `A` at trip `i`, so no weakening under `asn.exist` is required,
  and `loop_res_peel` is just `big_opL_app`.
- **`gen_loop_bounds_intro` + `loop_bound_le`** -- the bounds block is REBUILT
  at each trip, not framed: a walking pointer's `p+4 ≤ lenAddr` at trip n does
  NOT follow from the same bound at trip S n. Stated in `N`; the caller never
  touches `bv.bin`.
- **`asn_cell_inst`** -- the memory analogue of `asn_regidx_pts_inst`, which
  this plan recorded as missing. Needed when a cell CROSSES the back edge under
  a different address term and binder name. Note `@term_var _ x _ ctx.in_zero`:
  with an abstract `x : string`, `ctx.resolution` cannot compute the In-proof.

### NO contract changed

Not one `ls_extra_*`, not one `LoopSpec`, not one `solve_seg`. The two deficits
§3u measured on D turned out not to need the spec at all: the missing cells
come from the reservoir, and the dropped `p1 ≠ p7` is a PURE fact about the
valuation, so it is re-proved from arithmetic rather than carried.

### Reusability: TWO shapes cover all seven

`Example/ZZLoopTransCheck.v` -- all five previously-open back edges closed, no
admits, 50 s for the file.

| shape | loops | reservoir holds |
|---|---|---|
| every cell is new | D, F, Tail | both cells |
| SLIDING WINDOW, one cell crosses | B, C | one cell |
| no memory at all | divrem, A | nothing (`Fr` constant) |

The sliding-window case is the one that needed `asn_cell_inst`, and it also
carries a trap worth stating: the reservoir must hold ONLY the genuinely new
cell. A reservoir holding both cells of an overlapping window would claim the
same address at two different trips, be unsatisfiable, and make the whole loop
theorem vacuous while still compiling.

Per-loop cost, measured: **49-60 code lines** of frame proof, and the SHAPE is
identical every time -- rebuild the bounds, frame the register block, move the
one advanced register with `asn_regidx_pts_inst`, rebuild any dropped pure
fact, take the new cells from the reservoir, cross the shared cell with
`asn_cell_inst`. **F was produced from D by pure textual renaming and compiled
unchanged**, which is the strongest evidence available that the shape is real
and not a per-loop reinvention.

### Two method notes

- A 2005 s compile of this file was **contention, not cost**: held `pet`
  sessions plus `coqc` exceeded the 14 GB box and it swapped. Re-measured alone:
  **50 s**. Same lesson as §3t, hit twice in one day -- an unattended wall-clock
  number is not evidence. Check `free`/`ps` before believing one.
- `iStopProof` bundles the WHOLE remaining proof-mode context into the
  entailment, so hoist a pure `assert` ABOVE the `iIntros` instead of stopping
  the proof mid-way to prove it. And `rewrite` with an `⊣⊢` does not fire
  inside a proof-mode goal -- `iApply (bi.equiv_entails_1_1 _ _ H)` does.

## 3w. Cutting the per-loop frame: 59 -> 40, and a rule (2026-09-12)

§3v left each loop's frame proof at 49-60 lines with an identical SHAPE, which
is the tell that something is missing from the library rather than from the
loops. Three rounds of cutting, all measured on D:

| | lines | what changed |
|---|---|---|
| §3v baseline | 59 | -- |
| + `loop_reg_shift`, `loop_cell_shift`, `bv_of_N_neq`, `lenAddr_lt_exp2` | 48 | the two MOVES and the two pure facts become lemmas |
| + `loop_frame_std` (with `gen_regs_at_inst`) | 45 | the STRUCTURE becomes a lemma |
| + `refine`-inferred bounds, bullet form for the shift | **40** | the argument lists stop being written out |

`loop_frame_std` is the one that matters conceptually: it says what a loop
frame IS -- `bounds ∗ regs ∗ extra`, where the first two are the same argument
every time -- so a per-loop proof is the bounds `Forall` plus the extra
entailment and nothing else. `gen_regs_at_inst` had to come BACK for it (it was
written once and deleted as unused, because `iFrame` crosses a register block at
a CONCRETE call site; over abstract valuations it does not).

### The rule, which cost a detour to learn

**Whenever you reach for a tactic, check whether a lemma does it better.** A
`loop_bounds` Ltac was written here and then removed: `loop_bound_le` already
WAS the lemma, and the only thing the tactic added was inferring the per-base
value from the goal -- which `refine` does:

```coq
{ repeat constructor.
  all: refine (loop_bound_le _ _ _ _ _ _ _); [cbn; reflexivity | lia | cbn; lia]. }
```

One line for every base of every loop, the value unified by `reflexivity`, and
the reasoning stays in a lemma that can be read, reused and re-proved. A tactic
that only wraps a lemma is vocabulary without content.

Two mechanical notes from the same round: `iApply` determines `i2` from the
goal but NOT `i1` (that one comes from a premise), so `loop_reg_shift`'s source
valuation must be written out while the target can stay `_`; and `cbn` is
needed before `lia` on a bounds side condition because the offset is still a
pair projection `(t, 4).2`.

### What the remaining 40 lines are

12 of statement, 26 of proof, and the proof is now four NAMED steps:
`loop_frame_std` (structure) / `loop_bound_le` (one line, all bases) /
`loop_reg_shift` (the advanced register) / `bv_of_N_neq` + `loop_res_peel` (the
dropped fact and the cell trade). Everything left is specific to the loop.
The other four loops still carry their §3v proofs; converting them is the same
mechanical edit and would land them at the same place.

## 3x. Per-loop frame: 59 -> 29 (2026-09-12)

Continuing §3w on the instruction that anything identical across examples
belongs in a lemma, endToEnd-style. Two more groupings, both measured on D and
then re-derived on F by pure renaming (29 lines each):

- **`loop_frame_obl` / `loop_edge`** -- the two things a caller proves per loop
  now have NAMES, so their statements stop being a dozen lines of re-spelled
  valuation. Same fix as `dvInv` for the assembly block; it is worth saying
  plainly that *statements* were a third of the cost every single time.
- **one `iFrame` replaces the conjunct-by-conjunct walk.** Once the ONE
  register that moved is converted with `loop_reg_shift`, a bare `iFrame`
  discharges the fixed register, both `secLeak` facts, both cells and the
  reservoir in one step. The eleven lines of `iSplitL`/`iSplitR` ritual that
  did this by hand are gone. (It costs ~4 s; that is the documented
  split-before-framing tradeoff, and at this size it is worth it.)

| | D | what it is |
|---|---|---|
| §3v | 59 | conjunct-by-conjunct, every valuation written out |
| §3w | 40 | move/structure lemmas, refine-inferred bounds |
| §3x | **29** | named obligations + one iFrame |

Of those 29: **8 are the loop's own numeric side conditions** (`iq + 116 ≤
lenAddr`, the no-underflow bounds, `pe ≠ p7e`), 2 are `Proof`/`Qed`, and 19 are
proof. The 19 break down as 3 structural (`apply loop_frame_std`, bounds), 4
opening the loop's own `ls_extra_*` (irreducible -- they are the loop's own
names), 1 intro, 6 the `loop_reg_shift` call, 1 `iFrame`, 3 the pure fact the
post drops, 1 the reservoir peel.

**What is left is loop-specific, not ritual**: which register advances and by
how much, which pure fact the postcondition drops, and the loop's bounds. The
one remaining candidate for grouping is `ls_extra_*` itself -- if it were
STRUCTURED data (walking registers / fixed registers / pure facts / cells) the
way `ls_regs` already is, a single `loop_extra_step` lemma would take the 6-line
shift call and the 3-line pure fact down to side conditions, and the four
opening lines with them. That is a change to `LoopSpec`'s fields and to all
seven spec blocks; NOT attempted here, and it is the honest next step.

C, Tail and B still carry their §3v proofs (51 / 49 / 60). Converting them is
the same mechanical edit that took F from 59 to 29.

## 3y. `ls_extra_*` as DATA -- built, verified on D, and it does NOT cut lines

Done as asked in §3x's "honest next step". The machinery is in place and D is
converted end to end. The line count is the surprise, and it is reported first
because it contradicts the reason for doing it.

### The blocker that was not one

§4 of this plan says a Σ-generic memory builder is not worth building: the base
has to be weakened under `asn.exist` and the only weakening to hand is
`subst _ sub_wk1`, a recorded Θ(|Σ|²) driver that `iFrame` cannot see through.
**That is true of a builder that takes TERMS.** A builder that takes a
variable's NAME together with its `In`-proof weakens nothing -- it re-derives
the variable at the wider context with `ctx.in_succ`, which is structural and
transparent. Measured 2026-09-12 on a three-line probe: a hand-written extra
and the built one are equal by `reflexivity`. That one experiment is what made
the rest possible, and it cost ~100 ms.

### What landed (696aed6b)

- `walk_reg` / `cell_spec` records, `addr_off` (which must emit the BARE term at
  offset zero, or a non-moving register stops matching what the executor
  builds), `gen_walk_a/_an`, `gen_cells_a/_an`, `gen_pures`, `gen_extra_a/_an`.
- `loop_extra_step` (GenCompose) on top of `gen_walk_step`, `gen_pures_interp`
  and `walk_secLeak`. A caller supplies three things, all its own: what each
  walking register evaluates to on both sides, the pure facts the post drops,
  and the cell trade with the reservoir.
- The walk, the pures and the cells are SEPARATE conjuncts of `gen_extra_*`.
  Threading a tail through the folds instead interleaves the reservoir with the
  walk and makes the induction fight the frame; keeping them apart is what lets
  the step be three independent lemmas.
- **`LoopSpec` is UNCHANGED.** `ls_extra_*` stay free-form `Assertion` fields
  and a probe simply defines its own with the builders, so nothing in the
  record, the contracts or `solve_seg` had to move. D's contract re-verifies
  through `solve_seg` unchanged (22 s).

### The measurement

| D's frame | lines |
|---|---|
| §3x, hand-written extra + one `iFrame` | **29** |
| §3y, extra from data + `loop_extra_step` | **34** |

The `Forall` bookkeeping (`apply List.Forall_cons`, one `exists` witness and two
`split`s per walking register) costs about what the single `iFrame` saved.
Collapsing the witness from `∃ x y, … ∧ x = y` to `∃ x, …` bought 3 lines back
and no more.

**So: the restructuring does not reduce per-loop lines.** What it does buy is
real but different -- both sides of a back edge are generated from ONE
description and cannot drift apart (§3u found D's two sides HAD drifted: the
post silently dropped `p1 ≠ p7`), and the remaining proof is driven by the data
rather than by naming conjuncts in an `iSplit` walk.

### Not converted

F, C, Tail and B still use their hand-written extras and their §3v/§3x proofs,
and all still compile. Converting them is ~4× the same mechanical work for a
line count that measures neutral-to-worse, so it is a judgement call rather than
an obvious win -- parked for a decision rather than done on momentum.

## 3z. ALL FIVE loops go through the same lemma (2026-09-13)

§3y stopped after D because the line count had gone 29 -> 34 and that seemed
like a reason to stop. It was not: **uniformity was the point, not brevity** --
one lemma taking the example-specific logic as arguments, the way
`cfg_instrs_endToEnd` takes a program. Converted F, Tail, C and B.

Every loop's frame proof is now literally this, with nothing else in it:

```coq
  unfold loop_frame_obl. pose proof lenAddr_lt_exp2.
  apply (loop_frame_std <spec> <iota (S n)> <iota n> <q> _ _ eq_refl).
  { repeat constructor.
    all: refine (loop_bound_le _ _ _ _ _ _ _); [cbn; reflexivity | lia | cbn; lia]. }
  cbn [ls_extra_an ls_extra_a <spec>]. unfold <X>_extra_an, <X>_extra_a.
  apply (loop_extra_step <X>_walk <X>_pures <X>_cellspecs _ _ _ _ _).
  - (* the walking registers, as N values *) ...
  - (* the pure facts the postcondition drops *) ...
  - (* the cell trade with the reservoir *) ...
```

All four contracts re-verify through `solve_seg` unchanged -- `LoopSpec` never
moved, a probe just defines its `ls_extra_*` with the builders.

| loop | frame lines | §3v baseline |
|---|---|---|
| D | 34 | 59 |
| F | 31 | 59 |
| Tail | **28** | 49 |
| C | 40 | 51 |
| B | 45 | 60 |
| total | **178** | 278 |

36% overall, but the number that matters is that the five proofs now differ
ONLY in their three arguments. Tail is the cheapest because it has no pure
facts at all (`lt_pures := []`); C and B are dearest because the cell trade is
a crossing rather than a hand-off -- and that is the one place the two SHAPES
still show:

- **D / F / Tail** -- every cell is new: the third argument is
  `rewrite loop_res_peel; iIntros "(_ & Hres & Hnew)"; iFrame`.
- **C / B** -- a sliding two-cell window: one cell CROSSES the edge under a
  different address term and binder name, so the third argument is
  `loop_cell_shift`. **The reservoir must hold ONLY the genuinely new cell**
  (`lc_newcells` / `lb_newcells`); one holding both cells of an overlapping
  window would claim an address at two different trips, be unsatisfiable, and
  make the loop theorem vacuous while still compiling.

### Mechanical notes worth keeping

- `addr_off t off` must emit the BARE `t` when `off = 0`, or a register the
  loop does not move stops matching the term the executor builds.
- `cbn` must be told the record projections (`cs_pub cs_var cs_bind cs_off
  addr_off bv.eqb`) or the goal keeps whole `{| ... |}` literals in every
  position and `iIntros` runs past a 30 s timeout on a 20k-char goal.
- `iApply (loop_cell_shift "v0" "v1" _ _ _ _ x y)` -- leave the TERMS as `_`.
  Writing them out with explicit `ctx.in_succ` chains made unification thrash
  past the timeout; inferring them from the goal takes 190 ms.
- `repeat constructor` cannot be used on the walk `Forall`: it dives into the
  `exists` and picks evars. Write `apply List.Forall_cons` per element.
