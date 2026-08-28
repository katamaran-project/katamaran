# PLAN — `dropk`: drop dead logical variables with a projecting SymProp node

Successor to `PLAN-lvar-drop-build.md`, which is now the *investigation record*
and stays that. This is the executable build plan.

**Status: PHASES 0, 1 AND 2 ALL DONE. Phase 0 — the full per-step drop
obligation holds, `Qed` (§3bis). Phase 1 — both `ZZAccIndep` sources settled on
paper, the one non-obvious step mechanised (§4bis). **Phase 2 — the framework
change is LANDED and the kill-gate is GREEN** (2026-08-27, branch
`issue/dropk-framework`): `GATE_JOBS=1 ./scripts/gate.sh` reports build clean,
no proof holes, 14 end theorems axiom-clean. The point of no return has been
passed. NEXT: Phase 3, the liveness computation (CFGVer side) — and note §4bis's
finding that Phase 4 must thread `δ1`. No owner funding decision has been taken
on this page — see §0.**

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

> **SUPERSEDED by what Phase 2 actually built (2026-08-27) — and it is
> SIMPLER.** The `H : occurs_check … = Some pc'` argument above does not
> survive contact with `safe`/`psafe`/`wsafe`, which must be **total**: there is
> nowhere to get that proof term from inside a `SymProp` consumer. Instead
> `wdrop` makes the projected path condition total by falling back to the empty
> one, and then `acc_forget` needs **no side condition at all**:
>
> ```coq
> Definition wdrop (w : World) x {σ} {xIn : x∷σ ∈ w} : World :=
>   {| wctx := wctx w - x∷σ;
>      wco  := match occurs_check xIn (wco w) with Some pc' => pc' | None => ctx.nil end |}.
>
> Program Definition acc_forget {w} x {σ} {xIn : x∷σ ∈ w} : wdrop w x ⊒ w :=
>   acc_sub (sub_shift xIn) _.   (* Some: occurs_check_sound, then reflexivity.
>                                   None: everything entails the empty pc. *)
> ```
>
> The fallback is **conservative** — fewer assumptions reach the continuation,
> so its proposition is harder to prove, never easier — and is dead weight in
> practice, because the executor only emits `dropk` when the occurs-check
> succeeds. **When it succeeds, `wdrop w x` IS Phase 0's `zzw'`**, so
> `zz_dropk_step` applies verbatim and nothing in §3bis is invalidated.
>
> Trap for whoever writes the next call site: `acc_forget`'s trailing implicits
> make `x` *maximally inserted*, so `acc_forget x` is an "Illegal application
> (Non-functional construction)" error. Write `@acc_forget w x σ xIn`.

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

---

## §4bis PHASE 1 RESULT — both sources settled. GATE VERDICT: **GO**.

Settled 2026-08-27 by reading the real executor (`Verifier.v:686` / `:847`) and
the real refinement proof (`VerifierRel.v:699` / `:1350`), with the one
load-bearing new fact mechanised (`zz_persist_indep_future`, `Qed`, script
below, replays in 0.3 s).

### Source 1 — the recursive call. Settled, and §4's framing was WRONG.

§4 says this "comes from the induction hypothesis" and asks whether the IH is
strong enough. **The IH is not involved and the question does not arise.** The
IH (`VerifierRel.v:708`) is a *refinement* fact, `ℛ⟦□ᵣ(RVal -> RVal ->
RHeapSpec (RVal))⟧`; `ZZAccIndep` is a *syntactic equation* on the symbolic
side. A refinement fact cannot supply an equation, so no amount of
IH-strengthening would have helped — and none is needed.

What actually settles it: the recursive call in `sexec_cfg_addr`
(`Verifier.v:716`) is in **tail position**, and its entire ω-dependence is

```
persist_itableW (θ0∘θ1∘θ2∘θ3) tbl   persist_etable (…) exits   persist__term apc' θ3
```

i.e. persisted captured data and nothing else. If those occurs-check clean for
`x`, the two applications at `zz_fwd t1` and `zz_fwd t2` are **equal by
congruence** over `zz_persist_indep`. No induction, no IH, no new hypothesis.

Confirmed: the induction *is* on fuel and the IH *is* `□ᵣ`-boxed — exactly the
shape `zz_box_at_chosen` consumes — so Phase 0's lemma docks onto this proof
without reshaping it. That much of §4's expectation holds.

### Source 2 — the outer continuation. Settled, and localised to ONE object.

`sexec_triple_addr` (`Verifier.v:847`) ends:

```coq
⟨ θ3 ⟩ na <- sexec_cfg_addr fuel (zip_words (subst_itable ζ tbl) ws)
                            (subst_etable ζ exits) a2 (persist__term np θ2) ;;
let δ3 := persist δ1 (θ2 ∘ θ3) in
consume ens δ3.["an"∷ty_xlenbits ↦ na].
```

- `ens : Assertion (Σ ▻ "a" ▻ "an")` lives over the **fixed contract context Σ**
  and has *no world dependence at all*;
- `na` is an **argument** to the continuation, not a capture.

So **the entire ω-dependence of the outer continuation is `persist δ1`**, where
`δ1 = env.snoc (persist δ (θ1∘θ1')) _ (persist__term a θ1')`. That object *is*
§6's "ACCUMULATED TRANSLATION" root — the warning is confirmed, and now has a
name: **δ1**.

Discharge route: `zz_persist_indep` gives `subst δ1 (sub_single xIn t) = δ1'`
for every `t`, so the two continuations coincide. Threading through the rest of
the run is `zz_persist_indep_future` (below).

### The new fact — why the bind does not break this

The continuation does **not** sit at `zzw'`. Monadic binding puts it at some
later `w3` reached by `ω' : zzw' ⊒ w3`, and the ambient continuation is
persisted as `four ω Φ = fun w3 ω' => Φ w3 (acc_trans ω ω')`. So what is needed
is independence of `t` in `subst a (sub_acc (acc_trans (zz_fwd t) ω'))`, for
**arbitrary** `ω'`. `zz_persist_indep_future` (`Qed`) closes that in three
rewrites — `sub_acc_trans`, `subst_sub_comp`, then `zz_persist_indep` twice.

This is the fact §4 did not anticipate and is the real content of Phase 1.

### DESIGN CONSEQUENCE — Phase 4 changes. `sexec_cfg_addr` must thread δ1.

`sexec_cfg_addr` takes only `tbl, exits, apc, anp`. **It does not have δ1**, so
the drop step cannot occurs-check it, so source 2 cannot be discharged by
computation — it would have to be a hypothesis about an opaque `Φ` quantified
inside `RHeapSpec`, which is exactly the kind of un-dischargeable premise §2bis
died on.

Fix, and it is small: **pass `δ1` into `sexec_cfg_addr` as a threaded, persisted
argument alongside `tbl`/`exits`, and add it to Phase 3's occurs-check roots.**

- `ζ` is **already computed at the call site** (`Verifier.v:868`) and already
  passed in *indirectly* via `subst_itable ζ tbl`. It is just not available as
  an object the drop step can check.
- **Do not pass `ζ` alone — pass `δ1`.** `δ1 = env.snoc ζ a2`, and `a2` is the
  executor's *initial* `apc`. Since `apc` is overwritten every trip, the current
  `apc` does **not** cover `a2`, which `δ3` still captures. Checking `ζ` + the
  live `apc` therefore leaves a hole; checking `δ1` does not.
- Occurs-checking `tbl` is **not** a substitute for occurs-checking `ζ`: a
  component of `ζ` unused by the table is invisible in `subst_itable ζ tbl` but
  still present in `δ3`.

### Instance and representation gaps found (Phase 2/3 work items)

1. **`OccursCheckLaws (Const A)` does not exist** — same pattern as Phase 0's
   `Chunk`. One line, verified: `constructor; intros; now constructor.`
2. **With it, the table SHAPE assembles for free**: `OccursCheckLaws (fun Σ =>
   list (Pair (Pair (STerm τ1) (STerm τ2)) (Const A) Σ))` closes by
   `typeclasses eauto` (verified). So Phase 3's liveness check on the tables
   needs no bespoke recursion — **provided** the table types are stated in the
   `Pair`/`Const` algebra, or given instances directly.
3. **The table types are bespoke and side-step the generic machinery.**
   `SInstrTableW := fun w => list (Term (wctx w) ty_xlenbits * Term (wctx w)
   ty_word * AnnotInstr)` (`Verifier.v:390`) with hand-rolled
   `persist_itableW` / `persist_etable` as `List.map` over `persist__term`
   (`:395`, `:397`) — **not** the generic `subst`. So `zz_persist_indep` does
   not apply to a table off the shelf. Phase 5 needs bridging lemmas
   `persist_itableW θ tbl = subst tbl (sub_acc θ)` (and `_etable`), or the
   independence proved directly by list induction. Either is routine; neither
   is free.

### What is NOT claimed

- `ZZAccIndep` is **not** discharged for the real `sΦ`. Phase 1's exit criterion
  is "settled on paper", and that is what this is: the route is identified, its
  one non-obvious step is mechanised, and the object that has to be checked is
  named. Actually discharging it is Phase 5.
- The δ1-threading change to `sexec_cfg_addr` is **not** implemented and its
  knock-on cost to `cexec_cfg_addr` / `rexec_cfg_addr` (an extra argument on a
  proof with a 300 s+ hang in its history) is **not** estimated.
- Nothing was measured. §0's ~3× is untouched by any of this.

### The script, verbatim (replays clean in one run, 0.3 s)

Position mode: `rocq_start(file="theories/Symbolic/Propositions.v", line=2722,
character=40)`.

```coq
Import ctx.notations ctx.resolution env.notations.
Import UL.logicalrelation UL.logicalrelation.notations.
Import iris.proofmode.tactics.
Open Scope ctx_scope.

(* Second missing framework instance, same shape as Phase 0's Chunk one. *)
#[local] Instance zz_occ_laws_const {A} : OccursCheckLaws (Const A).
Proof. constructor; intros; now constructor. Qed.

(* With it, the SInstrTableW SHAPE assembles with no bespoke work. *)
Goal forall (τ1 τ2 : Ty) (A : Type),
  OccursCheckLaws (fun Σ => list (Pair (Pair (STerm τ1) (STerm τ2)) (Const A) Σ)).
Proof. intros. typeclasses eauto. Qed.

Section ZZPhase1.
  Context (w : World) (x : LVar) (σ : Ty) (xIn : (x∷σ ∈ w)%katamaran).
  Context (pc' : PathCondition (wctx w - x∷σ)).
  Context (Hoc : occurs_check xIn (wco w) = Some pc').

  Definition zzw' : World := @MkWorld (wctx w - x∷σ) pc'.

  Lemma zz_wco_eq : wco w = subst pc' (sub_shift xIn).
  Proof.
    pose proof (occurs_check_sound xIn (wco w)) as HH.
    unfold OccursCheckSoundPoint in HH. rewrite Hoc in HH. now inversion HH.
  Qed.

  Program Definition zz_fwd (t : Term (wctx w - x∷σ) σ) : w ⊒ zzw' :=
    @W.acc_sub w zzw' (sub_single xIn t) _.
  Next Obligation.
    intros t ι Hι. cbn in *.
    rewrite zz_wco_eq. rewrite subst_shift_single. exact Hι.
  Qed.

  Section ZZIndep.
    (* NB: the backtick form `{SubstLaws AT, OccursCheck AT, OccursCheckLaws AT}
       silently generates DUPLICATE Subst/OccursCheck instances and then
       `rewrite subst_shift_single` fails with "matches but type classes
       inference fails".  Name the instances explicitly. *)
    Context {AT : LCtx -> Type} {SubstAT : Subst AT} {OccAT : OccursCheck AT}
            {SubstLawsAT : SubstLaws AT} {OccLawsAT : OccursCheckLaws AT}.

    (* §2ter result 4, re-proved: Phase 1's linchpin. *)
    Lemma zz_persist_indep (a : AT (wctx w)) (a' : AT (wctx w - x∷σ))
        (Ha : occurs_check xIn a = Some a') (t : Term (wctx w - x∷σ) σ) :
      subst a (sub_single xIn t) = a'.
    Proof.
      pose proof (occurs_check_sound xIn a) as HH.
      unfold OccursCheckSoundPoint in HH. rewrite Ha in HH. inversion HH; subst.
      now rewrite subst_shift_single.
    Qed.

    (* PHASE 1's NEW FACT.  x-free captured data persists to the SAME thing
       along every witness THROUGH AN ARBITRARY FUTURE ACCESSIBILITY.  This is
       what makes ZZAccIndep survive the monadic bind: the continuation does
       not sit at zzw', it sits at some w3 reached from zzw' by ω'. *)
    Lemma zz_persist_indep_future (a : AT (wctx w)) (a' : AT (wctx w - x∷σ))
        (Ha : occurs_check xIn a = Some a')
        {w3 : World} (ω' : zzw' ⊒ w3) (t1 t2 : Term (wctx w - x∷σ) σ) :
      subst a (W.sub_acc (W.acc_trans (zz_fwd t1) ω'))
      = subst a (W.sub_acc (W.acc_trans (zz_fwd t2) ω')).
    Proof.
      rewrite !sub_acc_trans.
      rewrite !subst_sub_comp.
      cbn [W.sub_acc zz_fwd].
      rewrite (@zz_persist_indep a a' Ha t1).
      rewrite (@zz_persist_indep a a' Ha t2).
      reflexivity.
    Qed.
  End ZZIndep.
End ZZPhase1.
```

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

> **What Phase 2 ACTUALLY touched (2026-08-27) — the list above is
> incomplete.** Grepping `assume_vareq` as instructed found two consumers
> *outside* `Propositions.v`: `replay` in **`theories/Shallow/Monads.v`** and in
> **`theories/Symbolic/Monads.v`** (plus `replay_sound`'s bullet in the former).
> Neither is in §5's list. Also needed but unlisted: `size`, `count_nodes`,
> `dropk_prune` + `prune_dropk_sound`, `proper_dropk` / `proper_dropk_impl`
> instances (the two `push_plug` proofs need them), `weaken_symprop`,
> `uq_dropk`, `wsafe_safe`, `safe_debug_safe`, `erase_safe`, and a **parallel
> `edropk` constructor on the separate `ESymProp` inductive** with its four
> consumers — `Erasure` is two constructors' worth of work, not one case.
>
> **The trap that vos cannot catch**: `prune_angelic_binary_sound` and
> `prune_demonic_binary_sound` do `destruct p1; cbn; auto.` followed by **one
> bullet per constructor**. The match is still exhaustive, so `vos` is green and
> only a `full` compile fails, with "Attempt to save an incomplete proof". Any
> new `𝕊` constructor must add a bullet to **both**. The same shape is why
> `psafe_safe`'s `SymProp_ind` needs an extra `_` and a `11:` goal selector.
> Sites whose goal count is constructor-dependent, all of which had to be
> touched: `wsafe_safe`, `safe_debug_safe`, `prune_sound`, both `push_plug`s,
> `erase_safe`, `psafe_safe`, and the two binary prune lemmas.
> `ok_sound` (`MicroSail/SymbolicExecutor.v`) is bullet-free and unaffected.
>
> **Scope note on the kill-gate — resolved.** The gate compiles only
> `case_study/RiscvPmp` + `CFGVer`; MinimalCaps, BlockVer, BinaryBlockVer and
> `theories/Staging` are commented out of `_CoqProject`. **Owner confirms
> 2026-08-28 that all four are outdated dead code**, so "the framework change
> might break another case study" is not a live concern for this repo. A future
> `𝕊` constructor need not worry about them either.
- `acc_forget` in `Worlds.v`; the `psafe` case's `forgetting` lemma in
  `UnifLogic.v`.
- **`OccursCheckLaws Chunk` in `theories/Syntax/Chunks.v`**, next to
  `OccursCheckChunk` (`:188`). It does not exist and the heap side of Phase 0's
  lemma cannot be stated without it (§3bis). One line:
  `Proof. occurs_check_derive. Qed.` Pure addition — nothing depends on its
  absence, so it cannot break another case study. Do this FIRST; it is the one
  item in Phase 2 already known to work.
- **`OccursCheckLaws (Const A)` in `theories/Symbolic/OccursCheck.v`**, next to
  `OccursCheck_Const` (`:61`). Also missing, also one line
  (`constructor; intros; now constructor.`), also a pure addition. With it the
  instruction-table SHAPE resolves by `typeclasses eauto` (§4bis). Same slot as
  the `Chunk` one — do both together.
- Re-prove whatever breaks: `psafe_safe` (:2455) at minimum.

**Kill-gate: the whole project must still build.** `GATE_JOBS=1 ./scripts/gate.sh`.
Do this *before* writing any CFGVer code on top.

> **DONE 2026-08-27. GATE GREEN** — "build clean, no holes, 14 end theorems
> axiom-clean (only: `Machine.pure_decode` `Base.mmioenv`)". 65 files rebuilt.
> Commits `3cdaf029`, `d39d372e` (+ the bullet fix) on `issue/dropk-framework`.

**The `skill-path-guard` hook now demands `pred-modalities` on writes to
`Worlds.v`/`UnifLogic.v`, and `core-executor-internals` is NOT required for
`Propositions.v`** — read `pred-modalities` anyway; §7 of it is this design.

## §6 PHASE 3–6 — the CFGVer side. Carried over unchanged.

These are unchanged from `PLAN-lvar-drop-build.md` §3–§6 and were never
invalidated; that page's text is the reference, this is the summary.

> **PHASE 3 IS DONE, 2026-08-28, gate green** (34 files rebuilt, 14 end theorems
> axiom-clean). `all_ins` / `oc_ok` / `itableW_free` / `etable_free` /
> `var_dead` / `drop_candidate` / `find_dead` / `drop_dead` are in `Verifier.v`
> ahead of `sexec_cfg_addr`, **deliberately unwired** — wiring is Phase 4 and it
> changes the VC, which breaks `rexec_cfg_addr` until Phase 5. Dead code today.
>
> **The "dependent fold" never materialised.** `drop_dead` finds ONE dead
> variable, drops it, and RE-SCANS at the new world, recursing on fuel. Nothing
> is dependently folded, and `all_ins` is non-dependent too.
>
> Two traps, one iteration each:
> - **`ctx.remove` needs its `In`-proof BOUND FIRST**, so `drop_candidate` is a
>   NESTED `sigT` (`b`, then `bIn`, then the witness at `wctx w - b`). The flat
>   version fails with "cannot infer this placeholder".
> - **`@acc_subst_right` and `@SymProp.dropk` both need `@`** — trailing
>   implicits make their `x` maximally inserted, so the bare form silently
>   shifts `name b` onto the WITNESS slot. Third instance of this trap
>   (`acc_forget` and the Phase 0 section lemmas were the others); assume it for
>   any `{w} x {σ xIn} …` signature in this codebase.
>
> `SInstrTableW`/`SExitTable` have no `OccursCheck` instance, so the check is
> spelled out over their term columns rather than adding instances to
> `theories/`. The `AnnotInstr` payload is world-independent and cannot mention
> a logical variable.
>
> **Instrumentation is NOT built yet** and §6's warning stands. There is nothing
> to count until Phase 4 wires the step in. Route: a probe-file census of
> `dropk` nodes in the produced tree (as the `ZZ*.v` files already do), NOT an
> executor-side counter, which would perturb the term it measures.

**Phase 3 — liveness computation.** For each variable in `wctx w`, `occurs_check`
against **all** roots: `heap ∪ apc ∪ wco w ∪ tbl ∪ exits ∪ THE ACCUMULATED
TRANSLATION`. *The translation is a root and is easy to forget* —
`PLAN-unquantify-forward.md` omits it, and if the solver ever eliminated a
contract variable in favour of a term mentioning a per-trip variable, the outer
continuation mentions it once persisted while heap and path condition look clean.
Output a `Tri w w'`. Two fiddly parts, both plumbing: enumerating `wctx w` with
`In`-proofs, and the dependent fold. **Instrument it — emit how many drops
actually FIRE.** A drop that never fires is indistinguishable from one that works.

~~Note `dropk` needs no witness, so `ty.inhabit`'s `None` on tuple/union/record is
no longer a restriction — that under-approximation from the old design is gone.~~

> **WRONG — corrected 2026-08-28 against the types.** `dropk` needs no witness
> **in the tree**, which is what makes the refinement work. But the executor
> still needs one **in the accessibility**: `SHeapSpec A = □(A -> SHeap -> 𝕊)
> -> SHeap -> 𝕊` (`Symbolic/Monads.v:917`), so calling the continuation at the
> smaller world requires an `Acc w (wdrop w x)`, and `Acc`'s only non-reflexive
> constructor is `acc_sub ζ` with `ζ : Sub (wctx w) (wctx w - x∷σ)` — an `Env`
> with an entry for **every** variable of `wctx w`, `x` included. So a closed
> term of type σ over the smaller context is mandatory and `ty.inhabit`'s
> under-approximation **survives**.
>
> **Impact in practice: nil.** What we drop are havoced registers, which are
> `ty_xlenbits = bvec _`, and `inhabit (bvec n) = Some bv.zero`
> (`TypeDecl.v:973`). Only `enum` / `tuple` / `union` / `record` are undroppable.
>
> Useful corollary: since `𝕊` is indexed by **LCtx, not World**, and
> `wsubst w x t0` and `wdrop w x` have the same `wctx`, the executor may build
> the tree with the ordinary existing `acc_subst_right t0 : w ⊒ wsubst w x t0`.
> The two worlds are propositionally equal whenever
> `occurs_check xIn (wco w) = Some pc'` (by `subst_shift_single`), and that
> equality is needed only in the Phase 5 *proof*, never to typecheck the term.

> **§6's "dependent fold" difficulty is AVOIDABLE.** Do not compute a set of
> dead variables and remove them all at once — that is what forces a fold whose
> every step's type mentions the previous step's smaller context. Instead make
> the drop a **monadic loop over fuel**: find ONE dead variable, drop it as a
> single step, recurse and re-scan at the new world. Each drop is then an
> ordinary `SHeapSpec` step and nothing is dependently folded. Enumerating the
> context with `In`-proofs is likewise not dependent — it is
> `all_ins (Δ ▻ b) := existT b ctx.in_zero :: map (in_succ …) (all_ins Δ)`,
> every proof living at one fixed context.

**Phase 4 — executor step.** Inlined in `sexec_cfg_addr`, not an `sexec_ghost`
case: the step needs `tbl`, `exits`, `apc` and the translations, none of which a
ghost annotation can see. Gate behind a flag so the old path stays byte-identical
and A/B is one recompile apart.

> **The δ1 THREADING half of Phase 4 is DONE, 2026-08-28, gate green.**
> `sexec_cfg_addr` now takes `{Σ0} (trans : Sub Σ0 w)`, threaded and persisted
> like `tbl`/`exits` and otherwise unused, so the VC is unchanged — confirmed by
> the gate rebuilding 32 files with all 14 end theorems still axiom-clean.
> `sexec_triple_addr` passes `persist δ1 θ2`; its own signature is unchanged.
> `rexec_cfg_addr` takes `trans` as a fixed argument with **no relational
> premise** (the concrete executor has no logical variables), so
> **`cexec_cfg_addr` is UNTOUCHED** — that is what kept this cheap, and it also
> means Phase 5's re-pairing does not inherit an extra relation to maintain.
>
> Three traps, one build cycle each:
> - **`{w}` must be annotated `World`** once `trans` precedes the tables — `Sub`
>   takes an `LCtx`, so an inferred `w` elaborates as `LCtx` and
>   `SInstrTableW w` then fails.
> - **`persist_itableW_trans`/`persist_etable_trans` COLLAPSE** nested persists
>   into one composed accessibility; the generic `persist_trans` is stated in the
>   OPPOSITE (decomposing) direction. So `tbl`/`exits` arrive collapsed and
>   `trans` does not, and the association-normalising `assert` has nothing to
>   match until you add `rewrite <- ?(persist_trans (A := Sub Σ0))`.
> - **`persist x acc_refl` is DEFINITIONAL** (`persistent_subst` matches on the
>   accessibility), so the final `acc_refl` case needs no rewrite — unlike
>   `tbl`/`exits`, which need their `_refl` lemmas.
>
> `VerifierRel.v` built clean first time after those — no 300 s hang, no `rsolve`
> blowup.

> **PHASE 5 STATE, 2026-08-28. GATE IS RED; this is the open work.**
>
> Done and building: `acc_drop` (`Worlds.v`), `drop_dead` retargeted to `wdrop`
> via a convoy match, `cdrop_dead` + `mono_cdrop_dead` + `cdrop_binds` and the
> concrete bind in `cexec_cfg_addr`. `Verifier.vo` compiles.
>
> **The remaining obligation is `rdrop_dead`, and it needs `ZZAccIndep`.**
> `RHeapSpec RA` is literally `□ᵣ(RA -> RHeap -> ℙ) -> RHeap -> ℙ`, so the
> unfolded goal is Phase 0's `zz_dropk_step` line for line — **including its
> `Hindep` premise**, which is not optional:
>
> To use the box at the smaller world the fibre of `om` over ι must be
> inhabited, i.e. `inst t0 (ι∖x) = ι(x)`. For the executor's FIXED `t0` and
> arbitrary ι that is FALSE. Phase 0's way through is to read the witness off ι
> (legal — the box quantifies over ω and is instantiated after ι is in hand) and
> then bridge to the tree's `t0` with `ZZAccIndep`. There is no way to avoid the
> premise; it is the same quantifier-order gap that killed the `assume_vareq`
> design, and `dropk` survives it only because the witness is choosable at proof
> time.
>
> So `rdrop_dead` must be stated WITH the independence premise, and
> `rexec_cfg_addr` must thread it through its fuel induction — exactly §4's
> "it becomes a hypothesis on `rexec_cfg_addr` discharged once at the entry
> point". §4bis settled the discharge route: `sΦ`'s ω-dependence is persisting
> x-free data, and `var_dead` occurs-checks precisely those roots
> (`trans`/`tbl`/`exits`/`apc`/`anp`/heap/`wco`) — that is WHY it checks them.
>
> Also measured here: at `drop_fuel = 0` the bind does **not** collapse in the
> proof (`drop_fuel` is a `Definition`; `rsolve` will not unfold it), so there is
> no green intermediate checkpoint for the wiring. That is deliberate — it keeps
> the proof general in fuel — but budget for it.
>
> ### The premise must be BOTH sufficient AND closed under the recursion — two forms tried, both fail
>
> This is the real content of the remaining work, and it is NOT "apply Phase 0's
> lemma". `drop_dead` recurses at the shrunk world with continuation
> `four sΦ om`, so whatever premise `rdrop_dead` carries must survive that step.
> Two natural formulations, and why each is not enough:
>
> 1. **"`sΦ` depends on ω only through `sub_acc`"** —
>    `∀ w' (ω1 ω2 : w ⊒ w'), sub_acc ω1 = sub_acc ω2 → sΦ w' ω1 = sΦ w' ω2`.
>    **CLOSED** under `four` (since `sub_acc (om ∘ ω) = subst (sub_acc om)
>    (sub_acc ω)`), but **NOT SUFFICIENT**: the drop's two witnesses give
>    genuinely different substitutions, `sub_single xIn t1 ≠ sub_single xIn t2`,
>    so it says nothing about the case we need.
> 2. **The witness-specific form** (quantify `t1 t2` over drops of `w`'s own
>    variables, as §2ter's `ZZAccIndep` does) — **SUFFICIENT** for one step, but
>    **NOT CLOSED**: the recursive call needs the same property for drops at
>    `wdrop w x` composed with `om`, which is not an instance of the property at
>    `w`.
>
> So the premise has to say what §4bis established semantically: **`sΦ` FACTORS
> through persisted x-free data**.
>
> ### RESOLVED 2026-08-28 — `Factors` is both sufficient and closed, two `Qed`s
>
> ```coq
> Factors a sΦ  :=  ∃ g, ∀ w2 ω, sΦ w2 ω = g w2 (persist a ω)
> ```
>
> - **`factors_four` (`Qed`)** — CLOSED: `Factors a sΦ → Factors (persist a om)
>   (four sΦ om)`. And the new carrier `persist a om` is **exactly what
>   `drop_dead` already passes to its recursive call** — which is, in
>   retrospect, why the executor threads a carrier at all.
> - **`factors_witness_indep` (`Qed`)** — SUFFICIENT: with
>   `occurs_check xIn a = Some a'` (precisely what `var_dead` computes),
>   `sΦ w2 (acc_drop … t1 ∘ ω2) = sΦ w2 (acc_drop … t2 ∘ ω2)`. That is the whole
>   gap Phase 0's `Hindep` had to bridge, now discharged from x-freeness.
>
> Both are in `Example/ZZDropRefineProbe.v`, generic over any carrier `A` with
> `SubstLaws`/`OccursCheckLaws`. The blocker above is therefore CLEARED; what
> remains is assembly, not design:
> 1. state `rdrop_dead` with `Factors` and prove it by induction on fuel
>    (base from the box at `acc_refl`; drop case = Phase 0's script + the two
>    lemmas above + `zz_heap_transport`);
> 2. thread `Factors` through `rexec_cfg_addr`'s fuel induction;
> 3. discharge it once at `rexec_triple_addr`, where the carrier is `δ1`.
>
> Note the carrier at the real call site must cover EVERYTHING the ambient
> continuation captures — `trans`, `tbl`, `exits`, `apc`, `anp` — so instantiate
> `A` at their tuple. `var_dead` already occurs-checks each of them, which is
> what makes step 3 go through.
>
> **The carrier needs only `Subst`/`SubstLaws`, NOT `OccursCheck`.**
> `factors_witness_indep` only ever *uses* substitution-invariance, so state that
> (`WitnessBlind`) rather than an occurs-check. This is what makes a bundled
> carrier possible at all — the bundle has to cover `tbl`/`exits`, which
> deliberately have no `OccursCheck` instance. `witness_blind_of_oc` recovers it
> for any component that does have one, so componentwise checks feed the bundle.
>
> ### The scripts, verbatim
>
> **`Example/ZZDropRefineProbe.v` is GITIGNORED** (`.gitignore:33`,
> `case_study/RiscvPmp/CFGVer/Example/ZZ*`), so nothing in it survives on its
> own — these are recorded here for the same reason
> `PLAN-lvar-drop-build.md` §2bis records its own. Section context:
> `Context {A : LCtx -> Type} {SubstA : Subst A} {SubstLawsA : SubstLaws A}
> {OccA : OccursCheck A} {OccLawsA : OccursCheckLaws A}.`
> (`OccA`/`OccLawsA` are needed only by `witness_blind_of_oc`.)
>
> ```coq
> Definition Factors {w : World} (a : A (wctx w))
>     (sPhi : forall w2 : World, Acc w w2 -> Unit w2 -> SHeap w2 -> 𝕊 w2) : Prop :=
>   exists g : forall w2 : World, A (wctx w2) -> Unit w2 -> SHeap w2 -> 𝕊 w2,
>     forall (w2 : World) (om : Acc w w2), sPhi w2 om = g w2 (persist (A := A) a om).
>
> Lemma factors_four {w : World} (a : A (wctx w))
>     (sPhi : forall w2 : World, Acc w w2 -> Unit w2 -> SHeap w2 -> 𝕊 w2)
>     {w1 : World} (om : Acc w w1) :
>   Factors a sPhi -> Factors (persist (A := A) a om) (four sPhi om).
> Proof.
>   intros [g Hg]. exists g. intros w2 om2.
>   unfold four. rewrite Hg. now rewrite persist_trans.
> Qed.
>
> Definition WitnessBlind {w : World} {x : LVar} {σ : Ty}
>     (xIn : (x∷σ ∈ w)%katamaran) (a : A (wctx w)) : Prop :=
>   forall t1 t2 : Term (wctx w - x∷σ) σ,
>     subst a (sub_single xIn t1) = subst a (sub_single xIn t2).
>
> Lemma witness_blind_of_oc {w : World} {x : LVar} {σ : Ty}
>     {xIn : (x∷σ ∈ w)%katamaran} (a : A (wctx w)) (a' : A (wctx w - x∷σ))
>     (Ha : occurs_check xIn a = Some a') : WitnessBlind xIn a.
> Proof.
>   intros t1 t2.
>   pose proof (occurs_check_sound xIn a) as HH.
>   unfold OccursCheckSoundPoint in HH. rewrite Ha in HH.
>   inversion HH as [? Heq|]. rewrite Heq.
>   now rewrite !subst_shift_single.
> Qed.
>
> Lemma factors_witness_indep' {w : World} {x : LVar} {σ : Ty}
>     {xIn : (x∷σ ∈ w)%katamaran} {pc' : PathCondition (wctx w - x∷σ)}
>     (Hpc : occurs_check xIn (wco w) = Some pc')
>     (a : A (wctx w)) (Hbl : WitnessBlind xIn a)
>     (sPhi : forall w2 : World, Acc w w2 -> Unit w2 -> SHeap w2 -> 𝕊 w2)
>     (Hfac : Factors a sPhi)
>     (t1 t2 : Term (wctx w - x∷σ) σ) (w2 : World)
>     (om2 : Acc (@wdrop w x σ xIn) w2) :
>   sPhi w2 (acc_trans (@acc_drop w x σ xIn pc' Hpc t1) om2)
>   = sPhi w2 (acc_trans (@acc_drop w x σ xIn pc' Hpc t2) om2).
> Proof.
>   destruct Hfac as [g Hg]. rewrite !Hg. f_equal.
>   rewrite !persist_trans. f_equal.
>   rewrite !persist_subst. cbn. apply Hbl.
> Qed.
> ```
>
> Mechanics: the probe has **no `ModalNotations`**, so `⊒` is an "Undefined
> token" — write `Acc w w2`. And `@acc_drop` / `@wdrop` need the `@`
> (maximally-inserted `x`, the fifth instance of that trap).
>
> ### The persist/subst bridges — §4bis's flagged work item, DONE
>
> `Factors`'s carrier must bundle `tbl`/`exits`, whose `persist_itableW` /
> `persist_etable` are bespoke `List.map`s rather than generic `subst`. Both
> bridges are proved, and the `Subst`/`SubstLaws` instances they need resolve by
> `typeclasses eauto` **at the LCtx level** — note `SInstrTableW : TYPE` is
> `World -> Type` and `Subst` wants `LCtx -> Type`, so the type must be written
> out as `fun Σ : LCtx => list (Term Σ ty_xlenbits * Term Σ ty_word * AnnotInstr)`.
>
> ```coq
> Lemma zz_persist_itableW_subst {w1 w2 : World} (th : Acc w1 w2) (tbl : SInstrTableW w1) :
>   persist_itableW th tbl
>   = subst (T := fun Σ : LCtx => list (Term Σ ty_xlenbits * Term Σ ty_word * AnnotInstr))
>       tbl (sub_acc th).
> Proof.
>   unfold persist_itableW. cbn. destruct th; cbn.
>   - induction tbl as [|[[t x] i] tbl' IH]; cbn; [reflexivity|].
>     rewrite IH. now rewrite !subst_sub_id.
>   - induction tbl as [|[[t x] i] tbl' IH]; cbn; [reflexivity|].
>     now rewrite IH.
> Qed.
>
> Lemma zz_persist_etable_subst {w1 w2 : World} (th : Acc w1 w2) (exits : SExitTable w1) :
>   persist_etable th exits
>   = subst (T := fun Σ : LCtx => list (Term Σ ty_xlenbits)) exits (sub_acc th).
> Proof.
>   unfold persist_etable. destruct th; cbn.
>   - induction exits as [|t exits' IH]; cbn; [reflexivity|].
>     rewrite IH. now rewrite !subst_sub_id.
>   - induction exits as [|t exits' IH]; cbn; [reflexivity|].
>     now rewrite IH.
> Qed.
> ```
>
> ### `rdrop_dead` — statement settled, base case `Qed`, step case OPEN
>
> Stated **pointwise** (`… iota -> … iota`) per §10: the unary `⊢` will not
> parse after a binder, and the probe has no `ModalNotations`. `RProp` and
> `psafe` need the `LogicalSoundness.` prefix there.
>
> ```coq
> Lemma rdrop_dead {Sg0 : LCtx} (fuel : nat) : forall (w : World)
>     (trans : Sub Sg0 w) (tbl : SInstrTableW w) (exits : SExitTable w)
>     (apc anp : Term (wctx w) ty_xlenbits)
>     (cPhi : unit -> SCHeap -> Prop)
>     (sPhi : forall w2 : World, Acc w w2 -> Unit w2 -> SHeap w2 -> 𝕊 w2)
>     (ch : SCHeap) (sh : SHeap (wctx w))
>     (Hfac : Factors (dbundle trans tbl exits apc anp) sPhi)
>     (iota : Valuation w) (Hpc : instprop (wco w) iota),
>     ℛ⟦RBox (RImpl RUnit (RImpl RHeap LogicalSoundness.RProp))⟧ cPhi sPhi iota ->
>     ℛ⟦RHeap⟧ ch sh iota ->
>     LogicalSoundness.psafe (drop_dead fuel trans tbl exits apc anp sPhi sh) iota ->
>     cPhi tt ch.
> ```
>
> That is Phase 0's `zz_dropk_step` generalised to the fuel-indexed chain, with
> `Factors` the single premise. **`rdrop_dead_base` (fuel = 0) is `Qed`** —
> `drop_dead 0` is `SHeapSpec.pure tt`, so it is the box at `acc_refl`; note
> `specialize (H w acc_refl iota (inst_sub_id iota) Hpc)`, since
> `inst (sub_acc acc_refl) iota = iota` is NOT `eq_refl`.
>
> **The step case is the one thing still open.** Its ingredients are all proved:
> Phase 0's script, `factors_witness_indep'` (move the box's read-off witness to
> the tree's fixed one), `wb_bundle` (`WitnessBlind` from `var_dead`),
> `zz_heap_transport` (the heap), and `factors_four` + `dbundle_persist`
> (re-establish `Factors` at the recursive call).
>
> ### The premise machinery is COMPLETE — 11 `Qed`s
>
> With these, `rdrop_dead`'s only premise is `Factors (dbundle …) sΦ`:
> `factors_four` + `dbundle_persist` re-establish it at the recursive call, and
> `wb_bundle` + `factors_witness_indep'` kill the witness dependence at the drop.
> **`WitnessBlind` is a LEMMA from `var_dead`, not a premise** — which is
> precisely what makes the induction close, and is why the carrier must be
> literally the bundle the executor threads.
>
> - `wb_of_ocok` — `oc_ok` ⇒ `WitnessBlind`, for any component with an instance
> - `wb_etable`, `wb_itableW` — the same for the two bespoke tuple-lists, by list
>   induction (they have no `OccursCheck` instance, hence the elementwise route)
> - `dcarrier` / `dbundle` — the 5-tuple carrier; `Subst`/`SubstLaws` resolve by
>   `typeclasses eauto`
> - **`wb_bundle`** — `var_dead … = true` ⇒ `WitnessBlind xIn (dbundle …)`, at
>   ANY world, no extra premise. The keystone.
> - **`dbundle_persist`** — `persist (dbundle …) om = dbundle (persist trans om)
>   (persist_itableW om tbl) …`, i.e. the bundle commutes with persisting and the
>   RHS is *literally* what `drop_dead` hands its recursive call.
>
> Full scripts are in `Example/ZZDropRefineProbe.v` — **which is gitignored**, so
> if that file is lost they must be reconstructed from the shapes above.
>
> **`destruct th` FIRST, before the induction.** The obvious route —
> `apply List.map_ext` then `persist_subst` — fails twice over: `SubstList` is a
> FIXPOINT, not a `List.map`, so `map_ext` does not apply; and `cbn` unfolds
> `persist__term` to the instance body `persistent_subst`, after which
> `persist_subst` no longer matches syntactically. Case-splitting the
> accessibility sidesteps both, because `persistent_subst` is itself defined by
> matching on it.
>
> **Consequence for §11's risk register:** "`ZZAccIndep` not discharged for the
> REAL `sΦ`" is not a moderate residual — it is the whole of Phase 5's
> difficulty, and §4's "settled on paper" verdict covered the DISCHARGE ROUTE
> (x-free data persists identically) and not the STATEMENT problem above, which
> only appears once the premise has to survive a recursion. Do not read §4bis as
> saying this part is done.
>
> Probe for this work: `Example/ZZDropRefineProbe.v` (gitignored, outside
> `_CoqProject`, excluded from the gate's hole scan, so an `Admitted` there is
> harmless). It requires `Verifier` + `SpecIris` and NOT `VerifierRel`, so it
> iterates at `rocq_check` speed instead of recompiling the 900-line file blind.
> Rebuild its dependency closure after any `theories/` edit or it fails with
> "makes inconsistent assumptions over library …".

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
| ~~`ZZAccIndep` not dischargeable for the recursive call~~ | **RETIRED** | §4bis, 2026-08-27. The recursive call is congruence over `zz_persist_indep`, not an IH question at all; the outer continuation reduces to `δ1` alone |
| `sexec_cfg_addr` must now thread `δ1`, so `cexec_cfg_addr` / `rexec_cfg_addr` gain an argument | moderate — **NEW, found by §4bis** | unavoidable: without it source 2 is a hypothesis about an opaque `Φ`, which is what §2bis died on. Cost lands in Phases 4-5, on a file with a 300 s+ hang in its history. Not estimated |
| `ZZAccIndep` not discharged for the REAL `sΦ` (as opposed to on paper) | moderate | Phase 5. §4bis identifies the route and names the object; the table types' bespoke `persist` needs bridging lemmas first |
| ~~the ~10 `𝕊` cases break another case study~~ | **RETIRED — no caveat** | gate green 2026-08-27. The gate does not compile MinimalCaps / BlockVer / BinaryBlockVer / `theories/Staging`, but **the owner confirms (2026-08-28) all four are outdated DEAD CODE**. There is no other live case study to break, so this risk is void rather than merely untested. Do not re-raise it |
| ~~`prune` / `Erasure` cases turn out to be real research~~ | **RETIRED** | both were routine. The actual difficulty was elsewhere: tactic scripts whose GOAL COUNT tracks the constructor count, which `vos` cannot see (§5's box) |
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

**2026-08-27 — PHASE 1 CLOSED POSITIVE (§4bis).** Both `ZZAccIndep` sources
settled on paper against the real executor and refinement proof. Source 1 is
NOT an IH question — §4's framing was wrong; the recursive call is in tail
position and its ω-dependence is persisted captures, so it is congruence over
`zz_persist_indep`. Source 2 localises to exactly ONE object, `δ1`, because
`ens` is world-independent and `na` is an argument; `δ1` is §6's "accumulated
translation" root, now named. New mechanised fact `zz_persist_indep_future`
(`Qed`) carries independence through an arbitrary FUTURE accessibility, which is
what the monadic bind needs and §4 did not anticipate. **Found a required change
to Phase 4: `sexec_cfg_addr` must thread `δ1`** — it currently cannot see it, and
without it source 2 becomes an un-dischargeable hypothesis about an opaque `Φ`.
Two more missing instances found (`OccursCheckLaws (Const A)`; the tables' own
bespoke `persist_itableW`/`persist_etable` are not generic `subst`). Still
nothing built in `theories/`. **Next is Phase 2 — the point of no return.**

**2026-08-27 — PHASE 2 LANDED, KILL-GATE GREEN.** `dropk` constructor,
`wdrop`/`acc_forget`, the two missing `OccursCheckLaws` instances, and ~16
consumer cases across `Propositions.v`, both `Monads.v` files and
`Refinement/Monads.v`. `GATE_JOBS=1 ./scripts/gate.sh` passes: build clean, no
holes, 14 end theorems axiom-clean. Branch `issue/dropk-framework`, off
`issue/annot-havoc-spike`, unmerged.

Two things worth carrying forward. (1) **`acc_forget` needs no side condition** —
making `wdrop`'s path condition total (empty-pc fallback) removes the
`occurs_check … = Some pc'` argument §2 sketched, which mattered because
`safe`/`psafe`/`wsafe` cannot carry a proof term. (2) **The real hazard of
adding an `𝕊` constructor is not missing match cases** — those are exhaustive
and `vos` catches them — **it is tactic scripts whose goal count tracks the
constructor count**, which are green under `vos` and fail only under a full
compile, sometimes reporting the error at a bullet one past the real cause
(`refine_replay_aux` blamed its `debug` bullet). Three sites bit:
`prune_angelic_binary_sound`, `prune_demonic_binary_sound`, `refine_replay_aux`.

---

## §14 RESUME HERE — full state as of 2026-08-28

**Branch `issue/dropk-framework`** (off `issue/annot-havoc-spike`, which is
untouched and still gate-green). **THE GATE IS RED and every WIP commit says so.**
Phases 4b and 5 land together by construction, so there is no green intermediate
state; do not try to find one.

### What is DONE and gate-green (landed before the wiring)

Phases 0, 1, 2, 3, and the `δ1` threading. `theories/` carries `dropk`,
`wdrop`/`acc_forget`/`acc_drop`, and the two `OccursCheckLaws` instances
(`Chunk`, `Const`). `Verifier.v` carries the whole liveness computation.

### What is DONE but RED (the current edit)

- `Verifier.v`: `drop_dead drop_fuel` bound after `chunk_gc`; `drop_fuel := 0`.
  **Builds.**
- `VerifierRel.v`: `cdrop_dead` + `mono_cdrop_dead` + `cdrop_binds` + the
  concrete bind in `cexec_cfg_addr`. **Does NOT build** — `rexec_cfg_addr` has
  not been re-paired.

### `rdrop_dead` is CLOSED (2026-08-28) — `Qed`, axiom-clean

The step case closed the same day §14 was written. `rdrop_dead` now holds at
ARBITRARY fuel with `Factors (dbundle trans tbl exits apc anp) sΦ` as its single
premise, and `Print Assumptions` says **Closed under the global context**. The
whole probe file compiles green end to end (`coqc`, full mode, no `Admitted`).

Five lemmas were added to get there, all `Qed` (verbatim in §14.1):

- **`find_dead_sound`** — `find_dead` returns a bare `sigT` carrying no proof, so
  `var_dead`'s verdict is recovered by induction over the fold. Needed because
  `wb_bundle` consumes that verdict.
- **`factors_box_drop`** — THE step case's real content: the box TRANSPORTS across
  the drop. Phase 0 *consumed* the box at the drop; a fuel-indexed chain must hand
  one down instead. Instantiate at the witness read off ι (fibre inhabited by
  construction, so `assuming` cannot go vacuous), then slide to the tree's fixed
  `t0` via `factors_witness_indep'`.
- **`option_convoy`** — generic convoy elimination. A plain `destruct … eqn:` on
  `occurs_check bIn (wco w)` abstracts the motive's LHS as well and `acc_drop Hpc0 t0`
  stops typechecking. This lemma's `S` is a variable, so `destruct S` is legal.
- **`wco_wdrop` / `zz_heap_transport` / `zz_wco_eq`** — the three transports.
- **`rdrop_leaf`** — the leaf, stated at `sPhi w acc_refl tt sh` rather than
  `drop_dead 0 …`. See §14.1's comment: routing the leaf through `rdrop_dead_base`
  instead leaves SHELVED evars and `Qed` fails with no open goal shown.

Then, in order: thread `Factors` through `rexec_cfg_addr`'s fuel induction →
discharge once at `rexec_triple_addr` with carrier `δ1` → Phase 6 (absorb the new
bind in `sound_exec_cfg_addr_myWP2`) → Phase 7 (flip `drop_fuel`, measure, gate).

### How to get back to work in ~2 minutes

```
make -f Makefile.coq case_study/RiscvPmp/CFGVer/SpecIris.vo \
                     case_study/RiscvPmp/CFGVer/Verifier.vo
rocq_start(file="case_study/RiscvPmp/CFGVer/Example/ZZDropRefineProbe.v",
           line=<last line before `End DropRefineProbe.`>, character=8,
           force_restart=True)
```
Rebuild that closure after ANY `theories/` edit, or the probe fails with
"makes inconsistent assumptions over library …". The probe requires `Verifier` +
`SpecIris` and **not** `VerifierRel`, which is what keeps it usable while
`VerifierRel.v` is red.

### Standing traps (each cost at least one cycle)

1. **`{w} x {σ xIn}` signatures make `x` MAXIMALLY INSERTED.** A bare
   application silently shifts arguments onto the wrong slot. Hit five times
   (`acc_forget`, `acc_subst_right`, `SymProp.dropk`, `acc_drop`, `wdrop`).
   **Always `@`.**
2. **`ctx.remove` needs its `In`-proof bound first** — hence `drop_candidate` is
   a nested `sigT`.
3. **A new `𝕊` constructor breaks tactic scripts whose GOAL COUNT tracks the
   constructor count**, not just matches. `vos` is green; only a `full` compile
   fails, sometimes blaming a bullet one past the real cause.
4. **`destruct` the ACCESSIBILITY before any list induction.** `SubstList` is a
   `Fixpoint` not a `List.map`; and `cbn` unfolds `persist__term` to
   `persistent_subst`, after which `persist_subst` stops matching.
5. **In the probe:** no `ModalNotations`, so `⊒` is an "Undefined token" — write
   `Acc w w2`; `RProp`/`psafe` need the `LogicalSoundness.` prefix; `RSat`
   notation needs `Import logicalrelation logicalrelation.notations.`
6. **`( make …; echo "EXIT=$?" )` in a background job always reports 0** (that is
   `echo`'s status). Use `rc=$?; echo EXIT=$rc; exit $rc`, and read the log.
7. **`persist x acc_refl` is DEFINITIONAL**; `inst (sub_acc acc_refl) ι = ι` is
   `inst_sub_id`, **not** `eq_refl`.

### §14.1 The probe, VERBATIM

`Example/ZZDropRefineProbe.v` is **gitignored** (`.gitignore:33`), so this is the
only durable copy of these proof bodies. Header: copy `ZZGhostRefineProbe.v`'s
verbatim (everything up to its `Section` line) — it requires `Verifier` +
`SpecIris` and not `VerifierRel`.

```coq
Section DropRefineProbe.

  Import RiscvPmpCFGVerifExecutor.
  Import RiscvPmpCFGVerifShalExecutor.
  Import CStoreSpec (evalStoreSpec).
  Import CHeapSpec CHeapSpec.notations.

  (* Concrete mirror: the drop is the identity concretely. *)
  Definition cdrop_dead : CHeapSpec unit := fun POST h => POST tt h.

  (* ================================================================== *)
  (* THE PREMISE FOR rdrop_dead.                                        *)
  (*                                                                    *)
  (* Phase 0 carries `Hindep`; the difficulty is that rdrop_dead        *)
  (* RECURSES, so its premise must be both SUFFICIENT for one drop and  *)
  (* CLOSED under the recursive call.  Two natural forms each fail one  *)
  (* side (see PLAN-dropk.md §6):                                       *)
  (*   - "sPhi depends on omega only via sub_acc": closed, insufficient *)
  (*     (the two witnesses give different substitutions);              *)
  (*   - the witness-specific ZZAccIndep form: sufficient, not closed.  *)
  (*                                                                    *)
  (* `Factors` is both.  It says sPhi's omega-dependence FACTORS through *)
  (* persisting a carrier -- which is exactly §4bis's semantic claim,   *)
  (* made into a threadable hypothesis.                                 *)
  (* ================================================================== *)
  Section Fac.
    Context {A : LCtx -> Type} {SubstA : Subst A} {SubstLawsA : SubstLaws A}
            {OccA : OccursCheck A} {OccLawsA : OccursCheckLaws A}.

    (* Generic in the VALUE type V: rdrop_dead uses it at Unit (drop_dead returns
       nothing), but sexec_cfg_addr's own ambient continuation carries an
       STerm ty_xlenbits, and that is the Factors the drop's premise is derived
       from.  Nothing in the three lemmas below inspects V. *)
    Definition Factors {V : TYPE} {w : World} (a : A (wctx w))
        (sPhi : forall w2 : World, Acc w w2 -> V w2 -> SHeap w2 -> 𝕊 w2) : Prop :=
      exists g : forall w2 : World, A (wctx w2) -> V w2 -> SHeap w2 -> 𝕊 w2,
        forall (w2 : World) (om : Acc w w2), sPhi w2 om = g w2 (persist (A := A) a om).

    (* CLOSED: and note the new carrier is `persist a om`, which is EXACTLY
       what drop_dead already passes to its recursive call.  That is why the
       executor threads the carrier at all. *)
    Lemma factors_four {V : TYPE} {w : World} (a : A (wctx w))
        (sPhi : forall w2 : World, Acc w w2 -> V w2 -> SHeap w2 -> 𝕊 w2)
        {w1 : World} (om : Acc w w1) :
      Factors a sPhi -> Factors (persist (A := A) a om) (four sPhi om).
    Proof.
      intros [g Hg]. exists g. intros w2 om2.
      unfold four. rewrite Hg. now rewrite persist_trans.
    Qed.

    (* SUFFICIENT: an x-free carrier makes the continuation blind to the drop's
       witness, which is the whole gap Phase 0's Hindep had to bridge.  The
       x-freeness premise is `occurs_check xIn a = Some a'` -- precisely what
       var_dead computes. *)
    Lemma factors_witness_indep {V : TYPE} {w : World} {x : LVar} {σ : Ty}
        {xIn : (x∷σ ∈ w)%katamaran} {pc' : PathCondition (wctx w - x∷σ)}
        (Hpc : occurs_check xIn (wco w) = Some pc')
        (a : A (wctx w)) (a' : A (wctx w - x∷σ))
        (Ha : occurs_check xIn a = Some a')
        (sPhi : forall w2 : World, Acc w w2 -> V w2 -> SHeap w2 -> 𝕊 w2)
        (Hfac : Factors a sPhi)
        (t1 t2 : Term (wctx w - x∷σ) σ) (w2 : World)
        (om2 : Acc (@wdrop w x σ xIn) w2) :
      sPhi w2 (acc_trans (@acc_drop w x σ xIn pc' Hpc t1) om2)
      = sPhi w2 (acc_trans (@acc_drop w x σ xIn pc' Hpc t2) om2).
    Proof.
      destruct Hfac as [g Hg]. rewrite !Hg. f_equal.
      rewrite !persist_trans. f_equal.
      rewrite !persist_subst. cbn.
      pose proof (occurs_check_sound xIn a) as HH.
      unfold OccursCheckSoundPoint in HH. rewrite Ha in HH.
      inversion HH as [? Heq|]. rewrite Heq.
      now rewrite !subst_shift_single.
    Qed.
    (* factors_witness_indep needs only substitution-invariance of the carrier,
       not an occurs-check on it.  Saying so directly DECOUPLES the carrier from
       OccursCheck instances -- which matters, because the real carrier bundles
       tbl/exits and those deliberately have none (Verifier.v spells their check
       out over the term columns instead). *)
    Definition WitnessBlind {w : World} {x : LVar} {σ : Ty}
        (xIn : (x∷σ ∈ w)%katamaran) (a : A (wctx w)) : Prop :=
      forall t1 t2 : Term (wctx w - x∷σ) σ,
        subst a (sub_single xIn t1) = subst a (sub_single xIn t2).

    (* ...and it follows from the occurs-check for any component that has one,
       so componentwise checks feed a bundled carrier. *)
    Lemma witness_blind_of_oc {w : World} {x : LVar} {σ : Ty}
        {xIn : (x∷σ ∈ w)%katamaran} (a : A (wctx w)) (a' : A (wctx w - x∷σ))
        (Ha : occurs_check xIn a = Some a') : WitnessBlind xIn a.
    Proof.
      intros t1 t2.
      pose proof (occurs_check_sound xIn a) as HH.
      unfold OccursCheckSoundPoint in HH. rewrite Ha in HH.
      inversion HH as [? Heq|]. rewrite Heq.
      now rewrite !subst_shift_single.
    Qed.

    Lemma factors_witness_indep' {V : TYPE} {w : World} {x : LVar} {σ : Ty}
        {xIn : (x∷σ ∈ w)%katamaran} {pc' : PathCondition (wctx w - x∷σ)}
        (Hpc : occurs_check xIn (wco w) = Some pc')
        (a : A (wctx w)) (Hbl : WitnessBlind xIn a)
        (sPhi : forall w2 : World, Acc w w2 -> V w2 -> SHeap w2 -> 𝕊 w2)
        (Hfac : Factors a sPhi)
        (t1 t2 : Term (wctx w - x∷σ) σ) (w2 : World)
        (om2 : Acc (@wdrop w x σ xIn) w2) :
      sPhi w2 (acc_trans (@acc_drop w x σ xIn pc' Hpc t1) om2)
      = sPhi w2 (acc_trans (@acc_drop w x σ xIn pc' Hpc t2) om2).
    Proof.
      destruct Hfac as [g Hg]. rewrite !Hg. f_equal.
      rewrite !persist_trans. f_equal.
      rewrite !persist_subst. cbn. apply Hbl.
    Qed.
  End Fac.

  (* ================================================================== *)
  (* The premise machinery, complete.  Together these give rdrop_dead's  *)
  (* induction exactly what it needs, with `Factors (dbundle ...) sPhi`  *)
  (* as the ONLY premise:                                                *)
  (*   - at the recursive call, factors_four + dbundle_persist           *)
  (*     re-establish it;                                                *)
  (*   - at the drop, wb_bundle + factors_witness_indep' kill the        *)
  (*     witness dependence.                                             *)
  (* WitnessBlind is therefore a LEMMA from var_dead, not a premise --   *)
  (* which is what makes the induction close at all.                     *)
  (* ================================================================== *)

  Lemma wb_of_ocok {A : LCtx -> Type} {SubstA : Subst A} {SubstLawsA : SubstLaws A}
      {OccA : OccursCheck A} {OccLawsA : OccursCheckLaws A}
      {w : World} {x σ} (xIn : (x∷σ ∈ w)%katamaran) (a : A (wctx w)) :
    oc_ok xIn a = true -> WitnessBlind xIn a.
  Proof.
    unfold oc_ok. destruct (occurs_check xIn a) eqn:E; [|discriminate].
    intros _. exact (witness_blind_of_oc E).
  Qed.

  Lemma wb_etable {w : World} {x σ} (xIn : (x∷σ ∈ w)%katamaran) (l : SExitTable w) :
    etable_free xIn l = true ->
    @WitnessBlind (fun Sg => list (Term Sg ty_xlenbits)) _ w x σ xIn l.
  Proof.
    unfold etable_free. intros H t1 t2.
    induction l as [|t l' IH]; cbn in *; [reflexivity|].
    apply Bool.andb_true_iff in H as [H1 H2].
    rewrite (IH H2). f_equal. exact (wb_of_ocok xIn t H1 t1 t2).
  Qed.

  Lemma wb_itableW {w : World} {x σ} (xIn : (x∷σ ∈ w)%katamaran) (l : SInstrTableW w) :
    itableW_free xIn l = true ->
    @WitnessBlind (fun Sg => list (Term Sg ty_xlenbits * Term Sg ty_word * AnnotInstr)) _ w x σ xIn l.
  Proof.
    unfold itableW_free. intros H t1 t2.
    induction l as [|[[t v] i] l' IH]; cbn in *; [reflexivity|].
    apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff in H1 as [Ha Hb].
    rewrite (IH H2). f_equal. f_equal. f_equal.
    exact (wb_of_ocok xIn t Ha t1 t2).
    exact (wb_of_ocok xIn v Hb t1 t2).
  Qed.

  (* SIX components, not five.  `wd` (the instruction word out of lookup_instr)
     is captured by the drop's continuation -- step_after_drop persists it by
     theta_d like everything else -- so the Factors carrier must cover it or the
     witness does not exist.  It costs nothing operationally: var_dead's new
     conjunct is implied by itableW_free, since wd IS one of the table's words. *)
  Definition dcarrier (Sg0 : LCtx) : LCtx -> Type :=
    fun Sg => (Sub Sg0 Sg *
               list (Term Sg ty_xlenbits * Term Sg ty_word * AnnotInstr) *
               list (Term Sg ty_xlenbits) *
               Term Sg ty_xlenbits *
               Term Sg ty_xlenbits *
               Term Sg ty_word)%type.

  Definition dbundle {Sg0 : LCtx} {w : World}
      (trans : Sub Sg0 w) (tbl : SInstrTableW w) (exits : SExitTable w)
      (apc anp : Term (wctx w) ty_xlenbits) (wd : Term (wctx w) ty_word)
      : dcarrier Sg0 (wctx w) :=
    (trans, tbl, exits, apc, anp, wd).

  Lemma wb_bundle {Sg0 : LCtx} {w : World} {x σ} (xIn : (x∷σ ∈ w)%katamaran)
      (trans : Sub Sg0 w) (tbl : SInstrTableW w) (exits : SExitTable w)
      (apc anp : Term (wctx w) ty_xlenbits) (wd : Term (wctx w) ty_word)
      (h : SHeap (wctx w)) :
    var_dead xIn trans tbl exits apc anp wd h = true ->
    @WitnessBlind (dcarrier Sg0) _ w x σ xIn (dbundle trans tbl exits apc anp wd).
  Proof.
    unfold var_dead. intros H t1 t2.
    apply Bool.andb_true_iff in H as [H Hwd].
    apply Bool.andb_true_iff in H as [H Hex].
    apply Bool.andb_true_iff in H as [H Htbl].
    apply Bool.andb_true_iff in H as [H Hanp].
    apply Bool.andb_true_iff in H as [H Hapc].
    apply Bool.andb_true_iff in H as [H Htr].
    apply Bool.andb_true_iff in H as [Hpc Hh].
    unfold dbundle. cbn.
    f_equal. f_equal. f_equal. f_equal. f_equal.
    - exact (wb_of_ocok xIn trans Htr t1 t2).
    - exact (wb_itableW xIn tbl Htbl t1 t2).
    - exact (wb_etable xIn exits Hex t1 t2).
    - exact (wb_of_ocok xIn apc Hapc t1 t2).
    - exact (wb_of_ocok xIn anp Hanp t1 t2).
    - exact (wb_of_ocok xIn wd Hwd t1 t2).
  Qed.

  (* §4bis's flagged bridges.  destruct the ACCESSIBILITY first: SubstList is a
     Fixpoint not a List.map (so List.map_ext does not apply), and cbn unfolds
     persist__term to persistent_subst (after which persist_subst no longer
     matches syntactically).  Case-splitting the Acc sidesteps both. *)
  Lemma zz_persist_itableW_subst {w1 w2 : World} (th : Acc w1 w2) (tbl : SInstrTableW w1) :
    persist_itableW th tbl
    = subst (T := fun Sg : LCtx => list (Term Sg ty_xlenbits * Term Sg ty_word * AnnotInstr))
        tbl (sub_acc th).
  Proof.
    unfold persist_itableW. cbn. destruct th; cbn.
    - induction tbl as [|[[t v] i] tbl' IH]; cbn; [reflexivity|].
      rewrite IH. now rewrite !subst_sub_id.
    - induction tbl as [|[[t v] i] tbl' IH]; cbn; [reflexivity|].
      now rewrite IH.
  Qed.

  Lemma zz_persist_etable_subst {w1 w2 : World} (th : Acc w1 w2) (exits : SExitTable w1) :
    persist_etable th exits
    = subst (T := fun Sg : LCtx => list (Term Sg ty_xlenbits)) exits (sub_acc th).
  Proof.
    unfold persist_etable. destruct th; cbn.
    - induction exits as [|t exits' IH]; cbn; [reflexivity|].
      rewrite IH. now rewrite !subst_sub_id.
    - induction exits as [|t exits' IH]; cbn; [reflexivity|].
      now rewrite IH.
  Qed.

  (* CLOSURE at the value level: the bundle commutes with persisting, and the
     right-hand side is literally what drop_dead passes to its recursive call. *)
  Lemma dbundle_persist {Sg0 : LCtx} {w1 w2 : World} (om : Acc w1 w2)
      (trans : Sub Sg0 w1) (tbl : SInstrTableW w1) (exits : SExitTable w1)
      (apc anp : Term (wctx w1) ty_xlenbits) (wd : Term (wctx w1) ty_word) :
    persist (A := dcarrier Sg0) (dbundle trans tbl exits apc anp wd) om
    = dbundle (persist (A := Sub Sg0) trans om) (persist_itableW om tbl)
        (persist_etable om exits) (persist__term apc om) (persist__term anp om)
        (persist__term wd om).
  Proof.
    unfold dbundle, dcarrier.
    rewrite zz_persist_itableW_subst, zz_persist_etable_subst.
    unfold persist__term. destruct om; cbn; now rewrite ?subst_sub_id.
  Qed.

  (* ================================================================== *)
  (* rdrop_dead: the refinement of the drop chain.                       *)
  (*                                                                    *)
  (* Stated POINTWISE (`... iota -> ... iota`) per PLAN-dropk §10 -- the *)
  (* unary `⊢` will not parse after a binder here, and the probe has no  *)
  (* ModalNotations.  RProp/psafe need the LogicalSoundness. prefix.     *)
  (*                                                                    *)
  (* This is Phase 0's zz_dropk_step, generalised to the fuel-indexed    *)
  (* chain, with `Factors` as the SINGLE premise.                        *)
  (* ================================================================== *)
  Import logicalrelation logicalrelation.notations.

  Lemma rdrop_dead_base {Sg0 : LCtx} : forall (w : World)
      (trans : Sub Sg0 w) (tbl : SInstrTableW w) (exits : SExitTable w)
      (apc anp : Term (wctx w) ty_xlenbits) (wd : Term (wctx w) ty_word)
      (cPhi : unit -> SCHeap -> Prop)
      (sPhi : forall w2 : World, Acc w w2 -> Unit w2 -> SHeap w2 -> 𝕊 w2)
      (ch : SCHeap) (sh : SHeap (wctx w))
      (iota : Valuation w) (Hpc : instprop (wco w) iota),
      ℛ⟦RBox (RImpl RUnit (RImpl RHeap LogicalSoundness.RProp))⟧ cPhi sPhi iota ->
      ℛ⟦RHeap⟧ ch sh iota ->
      LogicalSoundness.psafe (drop_dead 0 trans tbl exits apc anp wd sPhi sh) iota ->
      cPhi tt ch.
  Proof.
    intros. cbn in *.
    unfold RBox, RImpl in H. cbn in H.
    unfold unconditionally, assuming in H.
    specialize (H w acc_refl iota (inst_sub_id iota) Hpc).
    cbn in H, H1.
    specialize (H tt tt).
    rewrite wand_unfold in H.
    specialize (H eq_refl ch sh).
    rewrite wand_unfold in H.
    specialize (H H0).
    unfold LogicalSoundness.RProp in H. cbn in H.
    rewrite wand_unfold in H. apply H.
    unfold SHeapSpec.pure, T in H1. exact H1.
  Qed.

  (* find_dead hands back a bare sigT with no proof attached, so var_dead's
     verdict has to be recovered by an induction over the fold.  cbn [List.fold_right]
     and NOT plain cbn: plain cbn normalises the LVar alias to string, after which
     the destruct's equation no longer matches syntactically. *)
  Lemma find_dead_sound {Sg0 : LCtx} {w : World}
      (trans : Sub Sg0 w) (tbl : SInstrTableW w) (exits : SExitTable w)
      (apc anp : Term (wctx w) ty_xlenbits) (wd : Term (wctx w) ty_word)
      (h : SHeap (wctx w)) (c : drop_candidate w) :
    find_dead trans tbl exits apc anp wd h = Some c ->
    var_dead (projT1 (projT2 c)) trans tbl exits apc anp wd h = true.
  Proof.
    unfold find_dead.
    generalize (all_ins (wctx w)) as l. intros l.
    revert c. induction l as [|p l' IH]; intros c; cbn [List.fold_right]; [discriminate|].
    destruct (List.fold_right _ None l') as [c'|] eqn:E.
    - exact (IH c).
    - destruct (var_dead (projT2 p) trans tbl exits apc anp wd h) eqn:Ev; [|discriminate].
      destruct (ty.inhabit (type (projT1 p))) as [v|]; [|discriminate].
      intros Hc. inversion Hc. cbn. exact Ev.
  Qed.

  (* BOX TRANSPORT ACROSS THE DROP -- the real content of rdrop_dead's step case.
     Phase 0 CONSUMED the box at the drop; the fuel-indexed chain must instead
     HAND ONE DOWN, so the box has to survive the world hop.

     The move is Phase 0's zz_box_at_chosen composed with factors_witness_indep':
     instantiate the box at `acc_trans (acc_drop t_iota) om2` with the witness READ
     OFF iota (which makes the fibre inhabited by construction, so `assuming` does
     not go vacuous), then slide from that witness to the tree's fixed t0.  The
     slide is exactly what Factors + WitnessBlind buy. *)
  Section BoxDrop.
    Context {A : LCtx -> Type} {SubstA : Subst A} {SubstLawsA : SubstLaws A}.

    Lemma factors_box_drop {w : World} {x : LVar} {σ : Ty}
        {xIn : (x∷σ ∈ w)%katamaran} {pc' : PathCondition (wctx w - x∷σ)}
        (Hpc : occurs_check xIn (wco w) = Some pc')
        (a : A (wctx w)) (Hbl : WitnessBlind xIn a)
        (cPhi : unit -> SCHeap -> Prop)
        (sPhi : forall w2 : World, Acc w w2 -> Unit w2 -> SHeap w2 -> 𝕊 w2)
        (Hfac : Factors a sPhi)
        (t0 : Term (wctx w - x∷σ) σ)
        (iota : Valuation w) (Hpci : instprop (wco w) iota) :
      ℛ⟦RBox (RImpl RUnit (RImpl RHeap LogicalSoundness.RProp))⟧ cPhi sPhi iota ->
      ℛ⟦RBox (RImpl RUnit (RImpl RHeap LogicalSoundness.RProp))⟧ cPhi
        (four sPhi (@acc_drop w x σ xIn pc' Hpc t0)) (inst (sub_shift xIn) iota).
    Proof.
      intros HB. unfold RSat, RBox in *. cbn in *.
      unfold unconditionally, assuming in *.
      intros w2 om2 iota2 Hfib Hpc2.
      specialize (HB w2 (acc_trans (@acc_drop w x σ xIn pc' Hpc
                                      (term_relval σ (env.lookup iota xIn))) om2) iota2).
      unfold four.
      rewrite (factors_witness_indep' Hpc Hbl Hfac t0
                 (term_relval σ (env.lookup iota xIn)) om2).
      apply HB; [|exact Hpc2].
      (* the fibre over iota is inhabited BY CONSTRUCTION: the witness was read off
         iota, so sub_single puts back exactly what sub_shift removed. *)
      cbn. rewrite sub_acc_trans. rewrite inst_subst. rewrite Hfib.
      cbn [sub_acc]. apply inst_sub_single_shift. reflexivity.
    Qed.
  End BoxDrop.

  (* CONVOY ELIMINATION.  drop_dead's inner match is a convoy -- it scrutinises
     `occurs_check bIn (wco w)` while its motive mentions that same term on the
     LEFT of the equation -- so a plain `destruct ... eqn:` abstracts the motive's
     LHS too and the branch's `acc_drop Hpc0 t0` stops typechecking (`o0 = Some pc'`
     is not `occurs_check bIn (wco w) = Some pc'`).  Abstracting the SCRUTINEE and
     the equation's RHS only is what this lemma packages: its `S` is a variable, so
     `destruct S` is legal, and the two branch obligations arrive with the equation
     intact. *)
  Lemma option_convoy {X : Type} {T : Type} {S : option X} {P : T -> Prop}
      (f : forall v : X, S = Some v -> T) (g : S = None -> T)
      (Hf : forall v (e : S = Some v), P (f v e))
      (Hg : forall e : S = None, P (g e)) :
    P (match S as o return S = o -> T with
       | Some v => f v
       | None   => g
       end eq_refl).
  Proof.
    revert f g Hf Hg. generalize (@eq_refl _ S).
    destruct S as [v|]; intros e f g Hf Hg; [apply Hf | apply Hg].
  Qed.

  (* Transport across the projection: path condition, dropped world's pc, heap. *)
  Lemma zz_wco_eq {w : World} {x σ} {xIn : (x∷σ ∈ w)%katamaran}
      {pc' : PathCondition (wctx w - x∷σ)}
      (Hoc : occurs_check xIn (wco w) = Some pc') :
    wco w = subst pc' (sub_shift xIn).
  Proof.
    pose proof (occurs_check_sound xIn (wco w)) as HH.
    unfold OccursCheckSoundPoint in HH. rewrite Hoc in HH. now inversion HH.
  Qed.

  (* `cbn [wco]`, NOT `cbn`: plain cbn normalises the LVar alias to string and
     then `rewrite Hoc` finds no subterm -- the same trap as find_dead_sound. *)
  Lemma wco_wdrop {w : World} {x σ} {xIn : (x∷σ ∈ w)%katamaran}
      {pc' : PathCondition (wctx w - x∷σ)}
      (Hoc : occurs_check xIn (wco w) = Some pc') :
    wco (@wdrop w x σ xIn) = pc'.
  Proof. unfold wdrop. cbn [wco]. now rewrite Hoc. Qed.

  Lemma zz_heap_transport {w : World} {x σ} {xIn : (x∷σ ∈ w)%katamaran}
      (sh : SHeap (wctx w)) (h' : SHeap (wctx w - x∷σ))
      (Hh : occurs_check xIn sh = Some h') (iota : Valuation w) :
    inst h' (inst (sub_shift xIn) iota) = inst sh iota.
  Proof.
    pose proof (occurs_check_sound (T := SHeap) xIn sh) as HH.
    unfold OccursCheckSoundPoint in HH. rewrite Hh in HH. inversion HH; subst.
    now rewrite inst_subst.
  Qed.

  (* THE LEAF.  Same content as rdrop_dead_base but stated at `sPhi w acc_refl tt sh`
     instead of `drop_dead 0 ...`, which matters: rdrop_dead reaches this leaf at
     FOUR places (fuel = 0, and the three degenerate branches of a step), and at
     three of them `trans`/`tbl`/`exits`/`apc`/`anp` are NOT determined by anything
     in the conclusion.  Going through rdrop_dead_base there leaves them as SHELVED
     evars and `Qed` fails with "the proof term is not complete" -- with no open goal
     shown.  Dropping the executor arguments from the leaf's statement removes the
     underdetermination at the source. *)
  Lemma rdrop_leaf {w : World}
      (cPhi : unit -> SCHeap -> Prop)
      (sPhi : forall w2 : World, Acc w w2 -> Unit w2 -> SHeap w2 -> 𝕊 w2)
      (ch : SCHeap) (sh : SHeap (wctx w))
      (iota : Valuation w) (Hpc : instprop (wco w) iota) :
    ℛ⟦RBox (RImpl RUnit (RImpl RHeap LogicalSoundness.RProp))⟧ cPhi sPhi iota ->
    ℛ⟦RHeap⟧ ch sh iota ->
    LogicalSoundness.psafe (sPhi w acc_refl tt sh) iota ->
    cPhi tt ch.
  Proof.
    intros H H0 H1. cbn in *.
    unfold RBox, RImpl in H. cbn in H.
    unfold unconditionally, assuming in H.
    specialize (H w acc_refl iota (inst_sub_id iota) Hpc).
    cbn in H, H1.
    specialize (H tt tt).
    rewrite wand_unfold in H.
    specialize (H eq_refl ch sh).
    rewrite wand_unfold in H.
    specialize (H H0).
    unfold LogicalSoundness.RProp in H. cbn in H.
    rewrite wand_unfold in H. apply H. exact H1.
  Qed.

  (* rdrop_dead: the same statement at arbitrary `fuel`, by induction, with
     `Factors` as the SINGLE premise.  This is Phase 0's zz_dropk_step generalised
     to the fuel-indexed chain.

     Four branches.  Three are leaves (fuel = 0; no dead variable found; the heap's
     own occurs-check fails) and go straight to rdrop_leaf.  The fourth is the drop:

       - option_convoy splits the convoy and hands back `e : occurs_check bIn (wco w)
         = Some v`, the equation acc_drop needs;
       - psafe of a dropk node IS `forgetting acc_forget`, so Hsafe arrives at the
         valuation `inst (sub_shift bIn) iota` -- exactly the IH's;
       - find_dead_sound + wb_bundle turn find_dead's verdict into WitnessBlind,
         which is what makes the box survive the hop (factors_box_drop);
       - factors_four + dbundle_persist re-establish Factors at the smaller world,
         and the carrier they produce is literally the tuple drop_dead already
         passes to its recursive call.  That is why drop_dead threads one. *)
  Lemma rdrop_dead {Sg0 : LCtx} (fuel : nat) : forall (w : World)
      (trans : Sub Sg0 w) (tbl : SInstrTableW w) (exits : SExitTable w)
      (apc anp : Term (wctx w) ty_xlenbits) (wd : Term (wctx w) ty_word)
      (cPhi : unit -> SCHeap -> Prop)
      (sPhi : forall w2 : World, Acc w w2 -> Unit w2 -> SHeap w2 -> 𝕊 w2)
      (ch : SCHeap) (sh : SHeap (wctx w))
      (Hfac : Factors (dbundle trans tbl exits apc anp wd) sPhi)
      (iota : Valuation w) (Hpc : instprop (wco w) iota),
      ℛ⟦RBox (RImpl RUnit (RImpl RHeap LogicalSoundness.RProp))⟧ cPhi sPhi iota ->
      ℛ⟦RHeap⟧ ch sh iota ->
      LogicalSoundness.psafe (drop_dead fuel trans tbl exits apc anp wd sPhi sh) iota ->
      cPhi tt ch.
  Proof.
    induction fuel as [|n IH];
      intros w trans tbl exits apc anp wd cPhi sPhi ch sh Hfac iota Hpc HB Hheap Hsafe.
    - exact (rdrop_leaf Hpc HB Hheap Hsafe).
    - cbn [drop_dead] in Hsafe.
      destruct (find_dead trans tbl exits apc anp wd sh) as [c|] eqn:Ec;
        [|exact (rdrop_leaf Hpc HB Hheap Hsafe)].
      pose proof (find_dead_sound trans tbl exits apc anp wd sh Ec) as Hdead.
      destruct c as [b [bIn t0]]. cbn [projT1 projT2] in Hsafe, Ec, Hdead.
      destruct (occurs_check bIn sh) as [h'|] eqn:Eh;
        [|exact (rdrop_leaf Hpc HB Hheap Hsafe)].
      revert Hsafe.
      (* %type: logicalrelation.notations overloads `->` as RImpl, so an unannotated
         motive is parsed in Rel scope and fails with "expected type Rel ?AT ?A". *)
      apply (option_convoy (P := fun s => (LogicalSoundness.psafe s iota -> cPhi tt ch)%type)).
      2: { intros _ Hsafe. exact (rdrop_leaf Hpc HB Hheap Hsafe). }
      intros v e Hsafe.
      cbn [LogicalSoundness.psafe] in Hsafe.
      unfold forgetting, acc_forget in Hsafe. cbn [sub_acc] in Hsafe.
      pose proof (wb_bundle bIn trans tbl exits apc anp wd sh Hdead) as Hbl.
      refine (IH (@wdrop w (name b) (type b) bIn) _ _ _ _ _ _ cPhi
                (four sPhi (acc_drop e t0)) ch h' _ (inst (sub_shift bIn) iota) _ _ _ Hsafe).
      + rewrite <- dbundle_persist. exact (factors_four _ Hfac).
      + rewrite (wco_wdrop e).
        apply (instprop_subst (sub_shift bIn) iota v).
        (* NOT `rewrite <- (zz_wco_eq e)`: the goal's `sub_shift bIn` is indexed by
           `b`, the lemma's by `MkB (name b) (type b)` -- convertible, not syntactically
           equal.  Rewriting in a COPY of Hpc, where `wco w` matches on the nose, and
           closing by conversion sidesteps it. *)
        pose proof Hpc as Hp. rewrite (zz_wco_eq e) in Hp. exact Hp.
      + exact (factors_box_drop e Hbl Hfac t0 Hpc HB).
      + exact (eq_trans (zz_heap_transport sh Eh iota) Hheap).
  Qed.

End DropRefineProbe.
```

---

## §15 THE HOIST — `step_after_drop`, and why the carrier grew to six (2026-08-28)

**Landed. `Verifier.v` builds; MvSwap, Jumps and Cmovznz4 rebuild clean, so the
computed VC is unchanged.**

### The problem it solves

`SHeapSpec.bind m f Φ = m (fun w1 θ1 a1 => f w1 θ1 a1 (four Φ θ1))`. So the
continuation `drop_dead` actually receives is

```
POSTd w1 θd _  =  ⟨the rest of the step at w1⟩ (four (four Φ θ0) θd)
```

`Factors` DOES hold for it — the persisted data is exactly the bundle, and
`four (four Φ θ0) θd` factors through `persist bundle θd` given `Factors` for the
outer `Φ` (rewrite the outer equation under the `fun w' ω' =>` binder, then
`persist_trans`; **no funext**, which matters — funext appears nowhere in
`theories/` and the gate admits only `pure_decode` and `mmioenv`).

But `Factors` is an EXISTENTIAL, so discharging it means exhibiting `g`, and `g`
is "the step body as a function of the bundle". Written inline, that witness would
have to be a hand-copy of the chain living in `VerifierRel.v` and kept in sync
with the executor by hand — the same staleness class as §14's trap 3.

### The fix

Hoist the post-drop chain into `step_after_drop` (`Verifier.v`), taking the bundle
explicitly. The continuation then IS `step_after_drop rec ai (persist tr0 θd) …
(four Φ' θd)`, so **`Factors`' witness is that definition** and there is nothing to
keep in sync. Every argument at the call site is literally `persist ⟨the same
thing drop_dead was given⟩ θd`; the `let tr0 := … in` block exists to make that
visible rather than to save typing.

Two facts worth recording:

- **The guard checker accepts `step_after_drop (@sexec_cfg_addr Σ0 n') ai …`.**
  The recursive call is applied to its decreasing argument, so passing the result
  as a function argument is fine. This was the main risk of the hoist and it did
  not materialise.
- **The persist layers SPLIT.** `persist wd (θ0 ∘ θd ∘ θ1)` becomes
  `persist (persist (persist wd θ0) θd) θ1` — propositionally equal by
  `subst_sub_comp`, NOT definitionally. Irrelevant to the VC (`vm_compute`
  normalises both identically, confirmed by the three examples), but it does
  change the term shape `rexec_cfg_addr` sees.

### Why the carrier is SIX components, not five

`step_after_drop` also consumes `wd`, the instruction word out of `lookup_instr`,
and persists it by `θd` like everything else. So `wd` is part of the continuation's
ω-dependence and the `Factors` carrier must cover it — otherwise the witness simply
does not exist. `dcarrier` / `dbundle` / `wb_bundle` / `dbundle_persist` /
`var_dead` / `find_dead` / `drop_dead` / `rdrop_dead` all gained the column.

**This is bookkeeping, not a soundness gap.** `var_dead`'s new conjunct
`oc_ok bIn wd` is IMPLIED by `itableW_free bIn tbl`, since `wd` is one of that
table's words — so no variable that used to be droppable stops being droppable.
It is listed explicitly only so the carrier can be read straight off the
conjunction.

### Also done here

`Factors` is now generic in the VALUE type `V`. `rdrop_dead` uses it at `Unit`
(the drop returns nothing), but `sexec_cfg_addr`'s ambient continuation carries an
`STerm ty_xlenbits`, and THAT is the `Factors` the drop's premise is derived from.
None of `factors_four` / `factors_witness_indep'` inspects `V`.

### What remains

1. `factors_drop_cont` — from `Factors a Φ` derive `Factors a` for the drop's
   continuation. With the hoist this is the rewrite-under-binder plus
   `persist_trans` described above; the witness is `step_after_drop` itself.
2. Restate `rexec_cfg_addr` to carry the `Factors` premise. **This is the
   remaining unknown**: its conclusion is currently `ℛ⟦… -> RHeapSpec (RVal …)⟧`,
   which universally quantifies the continuation, so the premise cannot be added
   without changing that shape — and `rsolve`'s instance search keys on it.
3. Fix the ω-numbering in `rexec_cfg_addr` (the drop's bind added a hop; the
   current failure is `line 808: The variable ω2 was not found`, i.e. purely the
   shift, nothing structural).
4. Discharge at `rexec_triple_addr`, carrier `δ1`. Then Phase 6, Phase 7.
