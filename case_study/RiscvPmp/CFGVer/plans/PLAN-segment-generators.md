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
                 (ia head : N) (prog : list AST) (skip take : nat)
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

## 6. Open

- **Port the two hand-written proofs onto this API.** `Example/ZZMladDvGen.v`
  (segment G's two contracts through `gen_seg_contract`, 79 lines vs 307) is
  written; the heavy port of `dv_step`/`dv_exit`/`dv_loop` onto
  `seg_step`/`seg_loop` is not yet a compiled artifact, though the fit was
  verified interactively against the real goals.
- **Gate coverage.** `GenCompose.vo` is listed explicitly in `gate.sh`'s
  `BUILD_TARGETS` because nothing in `Results.vo`'s closure Requires it yet.
  Drop it from that list once a tracked `Example/*Result.v` depends on it.
- **A dedicated skill.** `skill-path-guard.sh` currently maps the two new files
  onto existing skills. Per CLAUDE.md a new skill must be authored through
  `skill-creator`, not hand-written; that is the right follow-up rather than a
  hand-rolled `SKILL.md`.
