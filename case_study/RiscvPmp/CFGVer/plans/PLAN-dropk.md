# PLAN — `dropk`: drop dead logical variables with a projecting SymProp node

Successor to `PLAN-lvar-drop-build.md`, which is now the *investigation record*
and stays that. This is the executable build plan.

**Status: PHASE 0 CLOSED POSITIVE 2026-08-27 — the full per-step drop
obligation holds, `Qed`, with exactly the premises §3 pre-registered (see
§3bis). GATE VERDICT: GO to Phase 1. Design settled and de-risked by eight
`Qed`s across three sessions. No owner funding decision has been taken on this
page — see §0.**

**Read before doing anything:** `PLAN-lvar-drop-build.md` §2bis (why the obvious
design is FALSE) then §2ter (why this one is not). Do **not** read that page's
§2–§10, which are written for the refuted design; their content is carried
forward here where it survives. Do **not** read `PLAN-lvar-drop.md` at all except
its status block.

---

## §0 What is and is not decided

**Decided:** the *design*. `dropk` is self-contained — no new `Acc` constructor,
no change to `unconditionally`/`RBox`, no new modality (§2ter, four `Qed`s).

**Not decided, and this plan does not decide it:** whether the payoff justifies
the work. The measured prize is **~3× at n=16** on `br_divrem`, and R3's growth
exponent is 1.63 with the residual driver **unidentified** — so this is a factor,
not an exponent fix, and `|Σ|` is demonstrably not all of the wall. §8 prices it
cheaply and in parallel; run that first if you want the number before funding.

Nothing here unblocks anything. The landed 3-register havoc already reaches
`br_divrem`'s real 31 trips.

---

## §1 Established — do NOT re-derive

Eight `Qed`s (plus Phase 0's four supporting ones). All checked by position mode at
`rocq_start(file="theories/Symbolic/Propositions.v", line=2722, character=40)`.
Scripts are in `PLAN-lvar-drop-build.md` §2bis and §2ter; they replay in ~2 s.

**About soundness of the drop itself**

- `zz_drop_equiv` — dropping a variable and fixing it at an arbitrary value
  changes nothing, *no side condition*: the continuation's TYPE puts it at the
  smaller list, so the typing performs the occurs-check.
- `zz_pins` — the fused mint+drop pins the fresh variable. It is a rename, net
  `|Σ|` change zero. **Dead end; do not revisit.**

**About why the `assume_vareq` design is dead**

- `zz_drop_vacuous` — for *every* continuation `k`, `psafe (assume_vareq x t k) ι`
  already holds at any ι off the fibre.
- `zz_drop_step_strong_false` — the per-step obligation is FALSE even granting
  `occurs_check` deadness on heap *and* path condition and semantic
  insensitivity of the continuation. The counterexample's continuation is
  variable-free, so no hypothesis *about the continuation* can rescue it.
- There is no `Subst 𝕊` and there cannot be a generic one, so
  `weaken : 𝕊 (w-x) → 𝕊 w` is not definable.

**About why `dropk` is not dead**

- `zz_forgetting_stronger` — `forgetting zz_bwd Q ι → assuming (zz_fwd t) Q ι`,
  for any witness.
- **`zz_box_at_chosen`** — the money lemma. `unconditionally P ι` yields
  `P zzw' (zz_fwd (term_relval σ (env.lookup ι xIn))) (inst (sub_shift xIn) ι)`:
  the box delivers the continuation **at the shrunk valuation, with no vacuity,
  at every ι**.
- `zz_box_delivers_forgetting` — with `ZZAccIndep`, that is exactly the
  `forgetting`-strength payload `dropk` needs.
- `zz_persist_indep` — `subst a (sub_single xIn t) = a'` whenever
  `occurs_check xIn a = Some a'`, **for every `t`**. So x-free captured data
  persists identically along every witness; this is `ZZAccIndep`'s discharge
  route, and it is the same occurs-check §4 computes.

**About the full drop step (added by Phase 0, 2026-08-27)**

- `zz_dropk_step` — **the whole per-step obligation, `Qed`**. See §3bis. It is
  the line-by-line mirror of §2bis's `ZZDropStepObligationStrong`, which is
  FALSE; the only change is `dropk`'s `psafe`. Nothing else was weakened.
- `zz_heap_transport` / `zz_heap_rel_transport` — heap transport across the
  projection falls straight out of `occurs_check_sound` + `inst_subst`, exactly
  as §3 predicted. It was not the hard part.
- **`OccursCheckLaws Chunk` DOES NOT EXIST** in the tree — only the operation
  `OccursCheckChunk` (`Chunks.v:188`). So there is no `OccursCheckLaws SHeap`
  either (`occurs_check_laws_list` needs it), and heap transport has nothing to
  stand on until it is added. It is a **one-liner**,
  `Proof. occurs_check_derive. Qed.`, same idiom as `occurs_check_laws_formula`
  (`Formulas.v:301`). Phase 2 must add it; see §5.

**Structural facts worth not rediscovering**

- `Acc` has **two** constructors (`Worlds.v:280`): `acc_refl` and
  `acc_sub ζ (ent : wco w2 ⊢ subst (wco w1) ζ)`. Every named `acc_*` is a
  Definition. Adding an accessibility is a Definition, not a framework change.
- `subst_shift_single` holds for **any** `t`, so `wsubst w x t` is the *same
  world* for every witness. Witnesses change only `sub_acc`, never the target.
- `term_relval : ∀ {Σ} σ, RelVal σ → Term Σ σ` is a **constructor of `Term`**.
  Every value has a closed term at every context. This is what makes the
  per-ι witness choice legal.
- `|Σ|` costs **0.358 G words per variable at n=16**, and cost is precisely
  quadratic in `|Σ|` at fixed n (held-out 0.00%). But see §7's honesty clause —
  the naive quadratic extrapolation is known to over-estimate badly.
- The liveness premise holds and **depends on the register set**: 7-register
  havoc → all 7 droppable per trip; 3-register → 1 of 3. §7 re-measures this.

---

## §2 The design, concretely

```coq
(* theories/Symbolic/Propositions.v — new SymProp constructor, NO witness term *)
| dropk {Σ} (x : LVar) {σ} (xIn : x∷σ ∈ Σ) (k : 𝕊 (Σ - x∷σ)) : 𝕊 Σ

safe  (dropk x k) ι  :=  safe k (env.remove (x∷σ) ι xIn)
psafe (dropk x k)    :=  forgetting (acc_forget …) (psafe k)
```

```coq
(* theories/Symbolic/Worlds.v — five lines, obligation by occurs_check_sound *)
Definition acc_forget {w} x {σ} (xIn : x∷σ ∈ w) (pc' : PathCondition (w - x∷σ))
    (H : occurs_check xIn (wco w) = Some pc') : MkWorld (w - x∷σ) pc' ⊒ w
  := acc_sub (sub_shift xIn) _.
```

The whole design in one line: **keep the witness out of the trusted semantics and
in the accessibility, where a proof may still choose it per-ι.**

---

## §3 PHASE 0 — the full drop-step obligation. THE GATE. Hours, touches nothing.

§2ter settled the *box channel*. It did **not** prove the whole obligation: the
heap relation still has to transport across the projection, and the `RUnit` / ℙ
base cases still have to close.

Restate the complete per-step obligation in a probe, with `dropk`'s `psafe`
modelled as `forgetting zz_bwd (psafe …)` (faithful — that is its intended
definition) and `ZZAccIndep` assumed, and prove it. Mirror
`ZZDropStepObligationStrong` from §2bis so the two are comparable line by line.

Heap transport is the new work: you need `ℛ⟦RHeap⟧ ch sh` at ι to give
`ℛ⟦RHeap⟧ ch h'` at `ι∖x`, i.e. `inst h' (ι∖x) = inst sh ι` given
`occurs_check xIn sh = Some h'`. That should fall straight out of
`occurs_check_sound` + `inst_subst`; if it does not, say so.

| outcome | verdict |
|---|---|
| closes with `ZZAccIndep` and the occurs-check premises | **GO** to Phase 1 |
| closes only with an extra hypothesis | report it, then judge it against §4's dischargeability before continuing |
| does not close | **STOP** and report the residual goal verbatim |

Report before Phase 1 — decision checkpoint per `CLAUDE.md`.

---

## §3bis PHASE 0 RESULT — the full obligation HOLDS. GATE VERDICT: **GO**.

**`zz_dropk_step` closes with `Qed`**, 2026-08-27, at the §10 probe position.
`Print Assumptions` lists only the functor's own abstract parameters
(`𝑷`, `𝑯`, `varkit`, `typedeclkit`, `𝑹𝑬𝑮`, …) and the section variables — which
are precisely the premises — so **no proof holes and no extra axioms**. The
whole script below replays clean in **one run, 1.4 s**, from a cold
`force_restart` probe.

This is §3's exit-criteria **row 1**, with one qualification recorded in the
"extra requirement" heading below: the extra thing needed is not a *hypothesis*
about the executor, it is a missing framework *instance*, so it does not go to
row 2's "judge it against §4's dischargeability" — there is nothing to
discharge, only a one-liner to write.

### What was proved, and against what

`zz_dropk_step` is the line-by-line mirror of `ZZDropStepObligationStrong`
(`PLAN-lvar-drop-build.md` §2bis), which is **FALSE** (`zz_drop_step_strong_false`,
`Qed`). Same continuation quantification `ℛ⟦□ᵣ(RUnit -> RHeap -> ℙ)⟧`, same
`ℛ⟦RHeap⟧` heap premise, same conclusion at the enclosing world, same
occurs-check liveness premises. **The only thing changed is the symbolic side of
the conclusion** — `assume_vareq x t (…)` becomes `dropk`'s intended `psafe`,
i.e. `forgetting zz_bwd (psafe …)`. Nothing was weakened to make it go through:
§2bis's fallback (ii), semantic insensitivity of the continuation, is **not**
assumed here and is not needed.

That contrast is the result. It confirms §2ter's claim operationally: moving the
witness out of the trusted semantics and into the accessibility is *exactly* what
flips this obligation from false to provable.

### Premises actually used — the complete list

1. `Hoc : occurs_check xIn (wco w) = Some pc'` — Phase 3's liveness premise on
   the path condition. Doubles as `zz_bwd`'s well-formedness proof (§2ter).
2. `Hh : occurs_check xIn sh = Some h'` — Phase 3's liveness premise on the heap.
3. `Hindep : ZZAccIndep (fun w2 ω => ℛ⟦RUnit -> RHeap -> ℙ⟧ cΦ (sΦ w2 ω))` —
   assumed, per §3's brief. **This is now the whole remaining risk**, and it is
   Phase 1's subject.

No fourth premise appeared. In particular the `RUnit` base case closed by
`eq_refl` and the ℙ base case by `wand_unfold` — §3's "still have to close"
worry was unfounded.

### The one extra requirement, and it is NOT a hypothesis

**`OccursCheckLaws Chunk` does not exist in the tree.** `Chunks.v:188` defines
the *operation* `OccursCheckChunk` and nothing else; there is no laws instance,
hence no `OccursCheckLaws SHeap` (which `occurs_check_laws_list` would derive
from it), hence `occurs_check_sound` is not applicable to a heap at all and heap
transport cannot even be stated productively.

It is a **one-liner** — `Proof. occurs_check_derive. Qed.` — the same idiom
`occurs_check_laws_formula` uses at `Formulas.v:301`. Verified by `Qed` in the
script below. **Phase 2 must add it to `theories/Syntax/Chunks.v`**, next to
`OccursCheckChunk`. It is an addition, not a change: nothing existing depends on
its absence, so it cannot break another case study.

Worth noting *why* it was missing: nothing in the framework had ever needed to
occurs-check a heap before. That is a mild independent signal that the drop is
doing something the executor genuinely does not already do.

### Heap transport — resolved, and it was not the hard part

§3 flagged this as "the new work" and asked for a verdict. Verdict: it falls out
of `occurs_check_sound` + `inst_subst` in two lines, exactly as predicted, once
the instance above exists. `zz_heap_transport` gives
`inst h' (inst (sub_shift xIn) ι) = inst sh ι`, and `zz_heap_rel_transport`
wraps it at the `ℛ⟦RHeap⟧` level.

### Mechanics that cost time here — add to §10

- **`P` and `ι` are inferred IMPLICIT on these section lemmas**, so
  `zz_box_at_chosen PP ι Hpc HB` silently shifts arguments and reports
  `has type "∀ w2, w ⊒ w2 → Pred w2" while it is expected to have type
  "instprop (wco w) ?ι"`. **Apply every one of these lemmas with `@`.** Three
  separate detours came from this alone.
- **`RHeap`/`RInst`/`RImpl`/`RProp` are `simpl never`**; `cbn` will not touch
  them. `unfold RSat, RHeap, RInst, repₚ` (or `unfold RImpl` / `unfold RProp`)
  **first**, then `cbn`. The `pred-modalities` skill says this for
  `RSat`/`RBox`/`RImpl`; it applies to `RProp` and `RInst` too.
- **A goal at the smaller world cannot infer its world** from an `ℛ⟦RHeap⟧`
  application — `assert (Hh2 : ℛ⟦RHeap⟧ ch h' …)` fails with
  `expected to have type "SHeap (wctx ?w)"`. State it as
  `@RSat SHeap SCHeap RHeap ch zzw' h' …` and the world is pinned.
- `rewrite !wand_unfold` unfolds **all** nested wands at once, so the whole
  hypothesis chain arrives with a single `intros HB Hheap Hsafe`.

### The script, verbatim (replays clean in one run, 1.4 s)

Position mode: `rocq_start(file="theories/Symbolic/Propositions.v", line=2722,
character=40)`.

```coq
Import ctx.notations ctx.resolution env.notations.
Import UL.logicalrelation UL.logicalrelation.notations.
Import iris.proofmode.tactics.
Open Scope ctx_scope.

(* MISSING FRAMEWORK INSTANCE: there is no OccursCheckLaws Chunk in the tree,
   only OccursCheck Chunk (Chunks.v:188).  Without it there is no
   OccursCheckLaws SHeap and heap transport has nothing to stand on.
   One line, same idiom as occurs_check_laws_formula (Formulas.v:301). *)
#[local] Instance zz_occurs_check_laws_chunk : OccursCheckLaws Chunk.
Proof. occurs_check_derive. Qed.

Section ZZDropk.
  Context (w : World) (x : LVar) (σ : Ty) (xIn : (x∷σ ∈ w)%katamaran).
  Context (pc' : PathCondition (wctx w - x∷σ)).
  Context (Hoc : occurs_check xIn (wco w) = Some pc').

  Definition zzw' : World := @MkWorld (wctx w - x∷σ) pc'.

  Lemma zz_wco_eq : wco w = subst pc' (sub_shift xIn).
  Proof.
    pose proof (occurs_check_sound xIn (wco w)) as HH.
    unfold OccursCheckSoundPoint in HH. rewrite Hoc in HH. now inversion HH.
  Qed.

  Program Definition zz_bwd : zzw' ⊒ w := @W.acc_sub zzw' w (sub_shift xIn) _.
  Next Obligation.
    intros ι Hι. cbn in *. now rewrite <- zz_wco_eq.
  Qed.

  Program Definition zz_fwd (t : Term (wctx w - x∷σ) σ) : w ⊒ zzw' :=
    @W.acc_sub w zzw' (sub_single xIn t) _.
  Next Obligation.
    intros t ι Hι. cbn in *.
    rewrite zz_wco_eq. rewrite subst_shift_single. exact Hι.
  Qed.

  (* §2ter's money lemma, re-proved. *)
  Lemma zz_box_at_chosen (P : forall w2 : World, (w ⊒ w2) -> Pred w2)
      (ι : Valuation w) (Hpc : instprop (wco w) ι) :
    W.unconditionally P ι ->
    P zzw' (zz_fwd (term_relval σ (env.lookup ι xIn))) (inst (sub_shift xIn) ι).
  Proof.
    intros HB.
    specialize (HB zzw' (zz_fwd (term_relval σ (env.lookup ι xIn)))).
    unfold W.assuming in HB.
    apply HB.
    - cbn. rewrite inst_sub_single2. cbn.
      rewrite inst_sub_shift. apply env.insert_remove.
    - cbn. rewrite zz_wco_eq in Hpc.
      apply (instprop_subst (sub_shift xIn) ι pc'). exact Hpc.
  Qed.

  (* PHASE 0's new work #1: heap transport across the projection. *)
  Lemma zz_heap_transport (sh : SHeap (wctx w)) (h' : SHeap (wctx w - x∷σ))
      (Hh : occurs_check xIn sh = Some h') (ι : Valuation w) :
    inst h' (inst (sub_shift xIn) ι) = inst sh ι.
  Proof.
    pose proof (occurs_check_sound (T := SHeap) xIn sh) as HH.
    unfold OccursCheckSoundPoint in HH. rewrite Hh in HH. inversion HH; subst.
    now rewrite inst_subst.
  Qed.

  Lemma zz_heap_rel_transport (sh : SHeap (wctx w)) (h' : SHeap (wctx w - x∷σ))
      (Hh : occurs_check xIn sh = Some h') (ch : SCHeap) (ι : Valuation w) :
    ℛ⟦RHeap⟧ ch sh ι ->
    @RSat SHeap SCHeap RHeap ch zzw' h' (inst (sub_shift xIn) ι).
  Proof.
    unfold RSat, RHeap, RInst, repₚ. cbn.
    intros Hheap. rewrite (@zz_heap_transport sh h' Hh ι). exact Hheap.
  Qed.

  Definition ZZAccIndep (P : forall w2 : World, (w ⊒ w2) -> Pred w2) : Prop :=
    forall t1 t2 : Term (wctx w - x∷σ) σ, P zzw' (zz_fwd t1) = P zzw' (zz_fwd t2).

  (* PHASE 0's GATE: the FULL per-step drop obligation, dropk's psafe modelled
     as forgetting zz_bwd (psafe ...).  Mirrors ZZDropStepObligationStrong
     (PLAN-lvar-drop-build.md §2bis) line by line -- which is FALSE. *)
  Lemma zz_dropk_step
      (h' : SHeap (wctx w - x∷σ))
      (cΦ : unit -> SCHeap -> Prop)
      (sΦ : forall w2 : World, (w ⊒ w2) -> Unit w2 -> SHeap w2 -> 𝕊 w2)
      (ch : SCHeap) (sh : SHeap (wctx w))
      (t0 : Term (wctx w - x∷σ) σ)
      (Hh : occurs_check xIn sh = Some h')
      (Hindep : ZZAccIndep (fun w2 ω => ℛ⟦RUnit -> RHeap -> ℙ⟧ cΦ (sΦ w2 ω))) :
    ⊢ ℛ⟦□ᵣ (RUnit -> RHeap -> ℙ)⟧ cΦ sΦ -∗
      ℛ⟦RHeap⟧ ch sh -∗
      (W.forgetting zz_bwd (psafe (sΦ zzw' (zz_fwd t0) tt h')) -∗ ⌜cΦ tt ch⌝).
  Proof.
    constructor. intros ι Hpc _.
    rewrite !wand_unfold. intros HB Hheap Hsafe.
    pose proof (@zz_box_at_chosen
                  (fun (w2 : World) (ω : w ⊒ w2) => ℛ⟦RUnit -> RHeap -> ℙ⟧ cΦ (sΦ w2 ω))
                  ι Hpc HB) as HP.
    cbv beta in HP.
    unfold ZZAccIndep in Hindep.
    specialize (Hindep (term_relval σ (env.lookup ι xIn)) t0).
    cbv beta in Hindep.
    rewrite Hindep in HP.
    unfold RImpl in HP. cbn in HP.
    specialize (HP tt tt).
    rewrite wand_unfold in HP. specialize (HP eq_refl).
    specialize (HP ch h').
    rewrite wand_unfold in HP.
    specialize (HP (@zz_heap_rel_transport sh h' Hh ch ι Hheap)).
    unfold RProp in HP. cbn in HP.
    rewrite wand_unfold in HP.
    apply HP. exact Hsafe.
  Qed.

  Print Assumptions zz_dropk_step.
End ZZDropk.
```

## §4 PHASE 1 — settle `ZZAccIndep`'s threadability ON PAPER. Hours.

`PLAN-lvar-drop-build.md` §A.3 asked this for the old design and it was moot
there. **It is not moot here.** In the executor the drop sits mid-chain, so
`ZZAccIndep` is about the *composite* continuation. Two sources, both must be
settled before any `theories/` edit:

1. **the recursive call** — comes from the induction hypothesis. Check the
   induction is on fuel and that the IH is strong enough to carry it.
2. **the outer continuation**, from `rexec_triple_addr`. Its terms live over the
   contract's context and reach the current world by persistence, so
   `zz_persist_indep` should apply directly — that is the case this design was
   built for. It becomes a hypothesis on `rexec_cfg_addr` discharged once at the
   entry point.

**Exit:** both settled on paper → GO. Either one not dischargeable → **STOP**,
report which.

## §5 PHASE 2 — the framework change. Mechanical, broad, point of no return.

Only after Phases 0 and 1 close. This touches `theories/`, shared by every case
study.

- `dropk` constructor, plus its case in every `𝕊` consumer. In
  `Propositions.v` that is **~10**: `safe` (:329), `safe_debug` (:368),
  `wsafe` (:407), `prune` (:1215), two `ectx` walks (:1395, :1596), :1846,
  `uqSymProp` (:1938), `Erasure` (:2069), `psafe` (:2436). Find the rest by
  grepping `assume_vareq` — every site that matches on it needs a `dropk` case.
- **`prune` and `Erasure` are the two real proofs**; the rest is boilerplate.
  Budget accordingly.
- `acc_forget` in `Worlds.v`; the `psafe` case's `forgetting` lemma in
  `UnifLogic.v`.
- **`OccursCheckLaws Chunk` in `theories/Syntax/Chunks.v`**, next to
  `OccursCheckChunk` (`:188`). It does not exist and the heap side of Phase 0's
  lemma cannot be stated without it (§3bis). One line:
  `Proof. occurs_check_derive. Qed.` Pure addition — nothing depends on its
  absence, so it cannot break another case study. Do this FIRST; it is the one
  item in Phase 2 already known to work.
- Re-prove whatever breaks: `psafe_safe` (:2455) at minimum.

**Kill-gate: the whole project must still build.** `GATE_JOBS=1 ./scripts/gate.sh`.
Do this *before* writing any CFGVer code on top.

**The `skill-path-guard` hook now demands `pred-modalities` on writes to
`Worlds.v`/`UnifLogic.v`, and `core-executor-internals` is NOT required for
`Propositions.v`** — read `pred-modalities` anyway; §7 of it is this design.

## §6 PHASE 3–6 — the CFGVer side. Carried over unchanged.

These are unchanged from `PLAN-lvar-drop-build.md` §3–§6 and were never
invalidated; that page's text is the reference, this is the summary.

**Phase 3 — liveness computation.** For each variable in `wctx w`, `occurs_check`
against **all** roots: `heap ∪ apc ∪ wco w ∪ tbl ∪ exits ∪ THE ACCUMULATED
TRANSLATION`. *The translation is a root and is easy to forget* —
`PLAN-unquantify-forward.md` omits it, and if the solver ever eliminated a
contract variable in favour of a term mentioning a per-trip variable, the outer
continuation mentions it once persisted while heap and path condition look clean.
Output a `Tri w w'`. Two fiddly parts, both plumbing: enumerating `wctx w` with
`In`-proofs, and the dependent fold. **Instrument it — emit how many drops
actually FIRE.** A drop that never fires is indistinguishable from one that works.

Note `dropk` needs no witness, so `ty.inhabit`'s `None` on tuple/union/record is
no longer a restriction — that under-approximation from the old design is gone.

**Phase 4 — executor step.** Inlined in `sexec_cfg_addr`, not an `sexec_ghost`
case: the step needs `tbl`, `exits`, `apc` and the translations, none of which a
ghost annotation can see. Gate behind a flag so the old path stays byte-identical
and A/B is one recompile apart.

**Phase 5 — concrete mirror, then re-pair the refinement.** `cexec_cfg_addr`
gains `pure tt` (no logical variables concretely). `rexec_cfg_addr` re-paired
using Phase 0's lemma. **Budget for trouble**: this file has a 300 s+ compile hang
in its history whose root cause was never found, and `rsolve` has consumed
multiple GB. Develop in a probe, not in place. Skills: `cfgver-refinement`,
`cfgver-rsolve`.

**Phase 6 — absorb in adequacy.** `sound_exec_cfg_addr_myWP2` accounts for the
new step. Templates: `PLAN-chunk-gc.md` §12, and Phase 4 of `PLAN-annotinstr.md`
which did the same for `call_lemma`.

## §7 PHASE 7 — measure, then gate.

1. **RE-MEASURE THE REGISTER SET.** 7 registers make all 7 droppable, 3 make only
   1, so the landed "havoc three registers" advice is drop-conditional and **may
   invert**. Arms: `{3,7} registers × {drop on, drop off}` at n = 4, 8, 16, 31.
   Do not assume three still wins.
2. Protocol: `allocated_words`, baseline re-measured **on the commit**, one
   `Eval` per process, fuel `27n+60`, every cell classified `block` vs `error`.
3. Pre-registered criterion: **report the growth ratio, not a percentage.** A flat
   percentage off the top is not a fix.
4. Gate: `GATE_JOBS=1 ./scripts/gate.sh` — full build, no proof holes, 14 end
   theorems axiom-clean. Topic branch, `git merge --no-ff`.

## §8 PARALLEL, CHEAP, NON-BLOCKING — price it first if you want the number

Example-agnostic and unaffected by everything above: prepend `k` unused
existentials to a contract and measure. Run it on the whole-function examples,
`Example/BearSSLModpowFull.v` and `Example/BearSSLCheckScalar.v`, and report per
program: (1) its actual `|Σ|`, unknown for both at time of writing; (2) marginal
G words per declared variable there; (3) that marginal as a **fraction of the
program's total cost**.

Item 3 answers whether the `|Σ|` axis grows or shrinks in relative weight with
program size — the open question behind §0. An afternoon, no new machinery, and
it cannot mislead: a direct measurement on the programs that matter rather than
an extrapolation from the smallest one.

---

## §9 Do NOT retry these

- **The fused mint+drop.** `zz_pins`: it is a rename, net `|Σ|` change zero.
- **The `assume_vareq` design.** `zz_drop_step_strong_false`. Three hypothesis
  shapes die to one counterexample.
- **A post-pass over the finished tree** deleting dead `demonicv` binders. Sound,
  easy, and **saves nothing** — the `|Σ|` cost is paid during execution in solver
  lookups, not after the tree exists. `demonicv_prune` (`Propositions.v:1175`)
  already does this shape.
- **Naive `|Σ|²` extrapolation.** It says a flat world is worth 17.6× at n=16;
  the measured figure is ~3× by three routes that all over-estimate. Measure.

---

## §10 Mechanics that cost time in the last two sessions

- **Probe position:** `rocq_start(file="theories/Symbolic/Propositions.v",
  line=2722, character=40)` — the `Notation "'ℙ'"` line, which has `World`,
  `Pred`, `psafe`, `RProp`, `Rel`/`RSat`, `RHeap`, `unconditionally` and all three
  modalities in scope. Then `Import ctx.notations ctx.resolution env.notations`,
  `Import UL.logicalrelation UL.logicalrelation.notations`, `Open Scope ctx_scope`.
- **pet OOMs (>7.6 GB)** on position mode in `theories/Refinement/Monads.v` and on
  `Example/ZZGhostRefineProbe.v` past its `Lemma` line. State the *unfolded* form
  of a refinement obligation at the `Propositions.v` position instead — only
  `RHeapSpec`/`CHeapSpec` are unavailable there and the unfolded statement does
  not need them.
- **`LVar` is abstract inside the functor** — a literal name fails with `cannot
  unify "string" and "LVar"`. Use `Context (x : LVar)`, which also makes any
  counterexample stronger for being parametric.
- **`ctx.remove` needs its `In`-proof explicit** (`@ctx.remove _ (wctx w) b bIn`)
  or `cbn` stalls on an unresolved evar.
- **`⊢` collides.** `Import Entailment` brings the `InstProp` entailment, which
  shadows Pred's. Dodge it entirely: state Pred lemmas **pointwise**
  (`… ι -> … ι`) rather than as entailments. Costs nothing and avoids a
  ten-minute detour.
- **`crushPredEntails3` does not touch `RSat`/`RBox`/`RImpl`** — they are
  `simpl never`. `unfold RBox, RImpl` first, then `cbn`, then
  `rewrite !wand_unfold` to turn Pred wands into implications.
- **`occurs_check_sound` returns `OccursCheckSoundPoint`**, which is an
  `option.wlp`. Recipe: `pose proof (occurs_check_sound xIn a) as HH;
  unfold OccursCheckSoundPoint in HH; rewrite Ha in HH; now inversion HH`.
- **`Program Definition` obligations**: `intros` before rewriting, and split
  `rewrite a, b.` into separate sentences — the comma form hit a parse error in
  obligation mode.
- **Verify each `Qed` landed.** Nested proofs are allowed here, so a missing
  `Qed.` silently swallows a lemma. Check the feedback says "X is defined".

---

## §11 Risk register

| risk | severity | mitigation |
|---|---|---|
| ~~Phase 0's heap transport does not close~~ | **RETIRED** | closed 2026-08-27, `Qed` (§3bis). Two lines from `occurs_check_sound` + `inst_subst`, once `OccursCheckLaws Chunk` exists |
| `ZZAccIndep` not dischargeable for the recursive call | **high — now the ONLY open risk in the proof** | §4, settled on paper before any `theories/` edit. Phase 0 used no other premise, so this hypothesis alone stands between the design and a working drop step |
| the ~10 `𝕊` cases break another case study | moderate | Phase 2's kill-gate is a full build, run before any CFGVer work |
| `prune` / `Erasure` cases turn out to be real research | moderate | do those two first within Phase 2; if either resists, stop there rather than after the boilerplate |
| `rexec_cfg_addr` re-pairing hangs or OOMs | moderate | probe-first; precedent exists; `cfgver-rsolve` |
| drop never fires on the real program | moderate | Phase 3 instrumentation |
| the drop costs more than it saves | moderate | one state traversal per candidate variable per trip; a plausible outcome, not a bug |
| payoff is only ~3× | **accepted / undecided** | §0; §8 prices it |
| standing obligation: new executor cases and new `𝕊` functions must extend this | permanent | same burden already carried for the concrete mirror |

---

## §12 Honesty clauses (binding)

- Report the **growth ratio**, never a bare percentage.
- No wall-clock deltas under ~15% on this box without user-CPU or back-to-back
  runs — `.vo` page-cache state swings them by 2×.
- One heavy `Eval` per `coqc` process.
- `count_nodes = 1` does **not** mean discharged — it is 1 for `error` too.
  Classify `block` vs `error` explicitly, every cell.
- Any claim that a VC verifies must state whether proof holes remain.
- `rocq_compile_file` verifies TACTICS; only `make` verifies a FILE.
- If a phase fails, say so and stop. Nothing here is unblocking anything.
- This page has an ancestor that went through **six** verdicts before Phase A and
  a seventh after it. Do not trust any statement about this idea that is not in a
  status block backed by a named `Qed`.

---

## §13 Branch

Current work sits on `issue/annot-havoc-spike`, **unmerged**, gate green at
`6fc12d73`. Decide with the owner whether to merge that first or branch from it;
either way this is a topic branch and lands through
`GATE_JOBS=1 ./scripts/gate.sh` + `git merge --no-ff` (`branch-workflow` skill).

---

## Log

**2026-08-27 — plan opened**, superseding `PLAN-lvar-drop-build.md` after that
page's §2ter settled the re-scope positive. Design de-risked, nothing built,
no funding decision taken.

**2026-08-27 — PHASE 0 CLOSED POSITIVE (§3bis).** `zz_dropk_step` — the FULL
per-step drop obligation, the line-by-line mirror of the `assume_vareq`
obligation that is false — holds with `Qed`, assumptions clean, replaying in
1.4 s. Premises used: the two occurs-check liveness conditions and `ZZAccIndep`,
and nothing else; §2bis's continuation-insensitivity fallback was neither
assumed nor needed. Heap transport was not the hard part. One unbudgeted
discovery: `OccursCheckLaws Chunk` does not exist in the framework — a
one-liner, now a Phase 2 line item. **`ZZAccIndep` is now the sole open risk in
the proof**, which is exactly Phase 1's subject. Still nothing built in
`theories/`, still no funding decision.
