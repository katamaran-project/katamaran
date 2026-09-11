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
- `Post` must be a **parameter** of the per-trip lemma, not fixed to the
  invariant: `myWP2_loop` has no monotonicity lemma, so a trip-indexed
  invariant has to be reached from inside the step, not weakened afterwards.

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
