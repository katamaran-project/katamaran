---
name: pred-modalities
description: >
  The Pred/world/modality layer under every Katamaran refinement proof
  (theories/Symbolic/Worlds.v + UnifLogic.v): why a substitution runs BACKWARDS
  on valuations, what the FIBRE of an accessibility is, and the fact that
  `assuming` / `knowing` / `forgetting` are exactly the standard adjoint triple
  ∀_f ⊣ f* ⊢ ∃_f — knowing ⊣ forgetting ⊣ assuming, proved in the file. Read
  this whenever `assuming`, `knowing`, `forgetting`, `unconditionally`, `□ᵣ`,
  `sub_acc`, `Acc`/`⊒`, `sub_shift`/`sub_single`/`sub_wk1`, `repₚ`/`eqₚ`, or a
  `Pred w` shows up in a goal or definition and you need to know what it MEANS;
  before adding or changing an accessibility or a modality; and above all when a
  refinement hypothesis looks strong but turns out to prove nothing, or a
  `RefineCompat`/`rsolve` step stalls with a hypothesis you cannot use. The
  usual cause is a modality that has gone VACUOUS because the step's
  substitution pinned a variable and the fibre is empty — a mechanism invisible
  in the goal text. Framework-wide (theories/), not CFGVer-specific; a library
  skill.
---

# The `Pred` / world / modality layer

This is the layer every refinement proof stands on and the one people reach last.
It is small — three modalities and one flip — but the flip is genuinely
counterintuitive and the failure it causes (a hypothesis that is true and
useless) is invisible in the goal.

**The punchline first**, because it makes everything below fall into place. Write

```
f  :=  inst (sub_acc ω)  :  Valuation w2 → Valuation w1        for  ω : w1 ⊒ w2
```

Then the three modalities are substitution and its two adjoints, nothing more:

| Katamaran | standard | direction on facts | shape | can degenerate? |
|---|---|---|---|---|
| `forgetting ω` | pullback `f*` | earlier → later | apply `f` | **no** — total |
| `knowing ω` | `∃_f` (left adjoint) | later → earlier | `∃` over the fibre | **yes** — `False` |
| `assuming ω` | `∀_f` (right adjoint) | later → earlier | `∀` over the fibre | **yes** — `True` |

`knowing ⊣ forgetting ⊣ assuming` is Lawvere's `∃_f ⊣ f* ⊣ ∀_f`, and both halves
are theorems in the file (`UnifLogic.v:493,503`). If you carry away one thing,
carry away that "the fibre" is just the fibre of `f` and these are just `∀_f` /
`∃_f`.

## 1. A substitution runs backwards on valuations

`theories/Syntax/Terms.v:732`:

```coq
Definition Sub (Σ1 Σ2 : LCtx) : Set :=
  Env (fun b => Term Σ2 (type b)) Σ1.
```

Read it slowly: **for each variable of `Σ1`, a term built from `Σ2`'s variables.**
A table indexed by the *first* context whose entries live in the *second*.

That is what forces the flip. To evaluate `Σ1`'s variables you need values for
them; a `Sub Σ1 Σ2` plus values for `Σ2` gives you exactly that:

```
inst θ  :  Valuation Σ2  →  Valuation Σ1
```

Worked, because the abstract statement does not land on its own. Take
`θ = { a ↦ 2*m, b ↦ m } : Sub [a∷int, b∷int] [m∷int]`. Then
`inst θ [m↦k] = [a↦2k, b↦k]`, so:

- **forwards is total** — every `Σ2`-assignment yields a `Σ1`-assignment;
- **backwards is partial** — the image is exactly `{ a = 2b }`. Ask for a
  preimage of `[a↦8, b↦0]` and there is none.

> **The slogan.** A substitution says how to write the OLD variables using the
> NEW ones. Knowing the new values determines the old ones; never the reverse.

That partiality is the whole source of everything below. A substitution that
sends a variable to a term *pins* it, and assignments disagreeing with the pin
have no preimage at all.

## 2. Worlds, `Acc`, and what each step pins

A `World` (`Worlds.v:75`) is a variable context plus a path condition — a state
of knowledge. `Acc w1 w2`, written `w1 ⊒ w2` (`Worlds.v:280`), is a step from
`w1` to a *later* `w2`, and every step carries a substitution
(`Worlds.v:300`):

```coq
Definition sub_acc {w1 w2} (ω : w1 ⊒ w2) : Sub (wctx w1) (wctx w2)
```

Note the direction: `Sub w1 w2`, so by §1, `inst (sub_acc ω)` consumes a
*later* valuation and produces an *earlier* one. Two canonical steps, and they
differ only in whether they pin anything — which is the only thing that matters:

| step | `sub_acc` | pins? | preimages of a given earlier ι |
|---|---|---|---|
| `acc_snoc_right` (`Worlds.v:326`) — mint a variable | `sub_wk1` (`Terms.v:785`), each old variable ↦ itself | **no** | every `ι.[b↦v]`, one per `v` |
| `acc_subst_right x t` (`Worlds.v:381`) — substitute one away | `sub_single xIn t` (`Terms.v:806`), `x ↦ t` | **yes, `x`** | one, or **none** |

Concretely for the second row with `w = [x∷bool]` and `t = term_val ty.bool false`:
`ι = [x↦false]` has the empty assignment as its one preimage; `ι = [x↦true]` has
none. That is `[a↦8, b↦0]` from §1 again — same mechanism, same reason.

(`sub_shift bIn : Sub (Σ - b) Σ` at `Terms.v:780` runs the *other* way —
weakening, not shrinking. It is nobody's `sub_acc` among the steps above, but it
can perfectly well be one: `acc_sub (sub_shift xIn) _` is a legal **backward**
accessibility whenever `x` is dead in the path condition. See §7 — that turns
out to matter a lot.)

## 3. `Pred` and why entailment is pointwise

`Worlds.v:549`:

```coq
Definition Pred : TYPE := fun w => (Valuation w -> Prop)%type.
```

Every statement relating symbolic to concrete is a `Pred`, because a symbolic
object only *means* something at an instantiation — e.g. `repₚ`
(`Worlds.v:560`) is `λ ι, inst t ι = a`, which is what
`ℛ⟦RInst _ _⟧` / `RHeap` are built from.

And entailment is **one ι at a time** (`Worlds.v:594`):

```coq
Record entails (P Q : Pred w) : Prop :=
  MkEntails { fromEntails : forall ι, instprop (wco w) ι -> P ι -> Q ι }.
```

So inside any refinement proof you are always at a *single fixed* ι. There is no
`∀ι` left to lean on — it was consumed when the statement was introduced. Keep
that in view; it is what makes §6's degeneracy fatal rather than cosmetic.

## 4. The fibre, and why quantification is forced

You hold `ι : Valuation w1`. The step moved to `w2`, so the fact you want is a
`Pred w2` — it needs a `Valuation w2` before it says anything, and you have
none. All you have is `inst (sub_acc ω)`, which by §1 points the wrong way: it
*consumes* a `Valuation w2`. There is no map `Valuation w1 → Valuation w2`.

So you cannot pick an `ι'`; you can only quantify over the candidates, where the
only available notion of candidate is the one map you have:

```
ι' is a candidate for ι   ⟺   inst (sub_acc ω) ι' = ι          (the FIBRE over ι)
```

Two quantifiers, two modalities (`Worlds.v:755,757`), plus the total forward one
(`Worlds.v:759`):

```coq
assuming   ω Q ι  =  ∀ ι', inst (sub_acc ω) ι' = ι → instprop (wco _) ι' → Q ι'
knowing    ω Q ι  =  ∃ ι', inst (sub_acc ω) ι' = ι ∧ instprop (wco _) ι' ∧ Q ι'
forgetting ω Q ι  =  Q (inst (sub_acc ω) ι)
```

Which one goes where is forced too, and this is the useful intuition for
choosing at a call site: **receiving** a fact you must cover every possibility, so
`∀` — `assuming`; **asserting** one you get to choose a witness, so `∃` —
`knowing`. That maps onto demonic-vs-angelic, which is how you actually reach for
them. `forgetting` needs no quantifier at all because it runs earlier → later,
the one direction where `inst` already hands you what you need.

The adjunctions, and the four unit/counit lemmas you will actually rewrite with:

```coq
knowing_forgetting_adjoint  : (knowing ω P ⊢ Q)    <-> (P ⊢ forgetting ω Q)   (* UnifLogic.v:503 *)
forgetting_assuming_adjoint : (forgetting ω P ⊢ Q) <-> (P ⊢ assuming ω Q)     (* UnifLogic.v:493 *)

forgetting_assuming : forgetting ω (assuming ω P) ⊢ P      (* :991  *)
assuming_forgetting : P ⊢ assuming ω (forgetting ω P)       (* :997  *)
knowing_forgetting  : knowing ω (forgetting ω P) ⊢ P        (* :1003 *)
forgetting_knowing  : P ⊢ forgetting ω (knowing ω P)        (* :1009 *)
```

## 5. What a fat fibre buys you: the mint

`assuming_acc_snoc_right` (`UnifLogic.v:1248`) is the payoff case — a mint's
`assuming` is a genuine quantification over *all* values of the new variable:

```coq
Lemma assuming_acc_snoc_right {w b P} :
  assuming (w1 := wsnoc w b) acc_snoc_right P
    ⊣⊢ ∀ v, forgetting (acc_snoc_left acc_refl b (term_relval _ v)) P.
```

(The `forgetting` on the right is just "substitute `v` in".) So backward
transport is *not* inherently lossy. It is lossy exactly when the step pins.

## 6. The two degeneracy modes — the thing to actually remember

When the fibre over your ι is empty, both backward modalities collapse, dually:

| fibre over ι empty | `assuming` (∀) | `knowing` (∃) |
|---|---|---|
| value | `True` | `False` |
| as a hypothesis | **useless** — tells you nothing about `Q` | absurdly strong, but you will never *have* it |
| as a goal | trivially provable | unprovable |

The `assuming` column is the one that burns time, because nothing looks wrong.
You hold a hypothesis of the right shape, `iApply` it, and it yields nothing —
not because `Q` is false but because there is nothing for the `∀` to range over.
**Whenever a refinement hypothesis looks strong and proves nothing, check whether
the step's `sub_acc` pins a variable your ι disagrees with.**

Note the standard fact underneath: off the image of `f`, `∀_f` is `True` and
`∃_f` is `False`. Nothing Katamaran-specific.

`knowing_acc_subst_right` (`UnifLogic.v:1213`) states the relationship exactly,
and is the single most useful lemma in this file:

```coq
knowing (acc_subst_right t) P
  ⊣⊢ (eqₚ (term_var_in xIn) (subst t (sub_shift xIn)) ∗ assuming (acc_subst_right t) P)
```

Read: **`knowing` = fibre-inhabitedness ∗ `assuming`.** So upgrading a useless
`assuming` to a usable `knowing` costs you precisely one thing — a proof that the
fibre is inhabited, i.e. that `x` really does equal `t` at your ι. If you can
supply that equation, this lemma is your route. If you cannot, no amount of
massaging the modality will help, because that equation is the entire difference.

## 7. When a fibre looks empty: choose the witness at proof time

The reflex on meeting an empty fibre is "this transport is impossible". Often it
is not, and the way out is worth knowing because it is not visible in the goal.

**First, backward accessibilities are legal.** `Acc` has only two constructors
(`Worlds.v:280`) — `acc_refl` and `acc_sub ζ (ent : wco w2 ⊢ subst (wco w1) ζ)`.
Every named `acc_*` is a *Definition* over `acc_sub`. So nothing stops you
building `acc_sub (sub_shift xIn) _ : (w - x∷σ) ⊒ w`, provided you can discharge
the entailment — and if `occurs_check xIn (wco w) = Some pc'`, then
`occurs_check_sound` makes it **reflexivity**. `forgetting` along that
accessibility is a *total* `Pred (w-x) → Pred w`, no fibre, no vacuity. Adding an
accessibility is a Definition, not a framework change.

**Second, and this is the technique.** Suppose a step moves `w ⊒ (w - x∷σ)` with
`sub_acc = sub_single xIn t`, so it pins `x` and the fibre over your ι is empty
unless `ι(x) = inst t (ι∖x)`. If the witness `t` is baked into the *data* you are
reasoning about, you are stuck. But if `t` appears only in the *accessibility*,
you are not — because:

- `term_relval : ∀ {Σ} (σ : Ty), RelVal σ → Term Σ σ` is a **constructor of
  `Term`**, so every value has a closed term at every context; and
- `□ᵣ`/`unconditionally` quantifies over `ω`, and you instantiate that `∀`
  **after** you are handed ι.

So take `t := term_relval σ (env.lookup ι xIn)` — read the witness off ι — and the
fibre over ι is inhabited by construction. The box then hands you the
continuation at `ι∖x` with no vacuity, at *every* ι. Note also that
`subst_shift_single` holds for **any** `t`, so `wsubst w x t` is the *same world*
for every witness: the choice of `t` changes only `sub_acc`, never the target.

**The residual, when this technique applies**, is that the object you are
reasoning about was built with some *fixed* witness `t₀` while the box hands you
the one for `t`. That gap is an equation at a single world — no `𝕊`-weakening
needed — and it discharges for anything whose `ω`-dependence is *persisting
x-free data*, since `subst (subst a (sub_shift xIn)) (sub_single xIn t) = a`
(`subst_shift_single`) for every `t`.

**Worked all the way through, with `Qed`s**, on the dead-logical-variable drop:
`case_study/RiscvPmp/CFGVer/plans/PLAN-lvar-drop-build.md`. Read **§2bis first**
— it refutes, by counterexample, the design that bakes the witness into the tree
(`assume_vareq`), and three hypothesis shapes die with it — then **§2ter**, which
applies the technique above to the design that does not (`dropk`). The contrast
between the two is the practical lesson: *keep witnesses out of the trusted
semantics and in the accessibility, where a proof may still choose them.*

## 8. Where `assuming` reaches you: `□ᵣ`

You rarely write `assuming` by hand; it arrives inside the box on every
continuation. `Worlds.v:761`:

```coq
Definition unconditionally {w} : (□ Pred) w -> Pred w :=
  fun P => (∀ w2 (ω : w ⊒ w2), assuming ω (P w2 ω))%I.
```

and `RBox` (`UnifLogic.v:1406`), i.e. the `□ᵣ` of `ℛ⟦□ᵣ RA⟧`, is
`unconditionally` of the relation. So **`assuming` is the only door through which
a world-changing step can use its continuation's relation.** Every `RefineCompat`
instance and every `rsolve` step goes through it. A pinning step shuts the door.

## 9. Reading traps

- **`assuming` calls the LATER world's valuation `ιpast`**, and `forgetting`'s
  argument is `Rfut`. The names read backwards relative to `⊒`. Best guess: they
  track direction of travel along `f`, not along `⊒`. The file does not say.
- **The names are not settled terminology.** `Worlds.v:753`, directly above the
  definitions, reads `(* update: better/more standard names? *)`. If
  `assuming`/`knowing` feel unhelpful, that is not a comprehension failure —
  translate to `∀_f`/`∃_f` via the table at the top and move on. The names are
  good for the *use site* (assume vs. know ≈ demonic vs. angelic), poor for the
  *content*.
- `assuming`'s `∀` has **two** premises before it reaches `Q` — fibre membership
  *and* the later world's path condition. So "ι is outside the image" is
  sufficient for vacuity but not necessary; a contradictory later `wco` does it
  too.

## 10. Checking any of this interactively

These definitions are inside module functors, so preamble mode cannot reach them.
Use **position mode**, and prefer this position:

```
rocq_start(file="theories/Symbolic/Propositions.v", line=2722, character=40)
```

That is the `Notation "'ℙ'"` line at the end of `LogicalSoundness`, and it has
`World`, `Pred`, `psafe`, `RProp`, `Rel`/`RSat`, `RHeap`, `unconditionally` and
all three modalities in scope at once. Then `Import ctx.notations
ctx.resolution env.notations`, `Import UL.logicalrelation
UL.logicalrelation.notations`, and `Open Scope ctx_scope`.

Measured 2026-08-27: **pet OOMs (>7.6 GB) on position mode in
`theories/Refinement/Monads.v`**, so state the unfolded form of a refinement
obligation at the `Propositions.v` position instead — continuations, heaps and
`ℛ⟦…⟧` are all available there, and only `RHeapSpec`/`CHeapSpec` are not.

Two more mechanics inside the functor: `LVar` is abstract, so a literal variable
name will not typecheck (`cannot unify "string" and "LVar"`) — take
`Context (x : LVar)`, which also makes any counterexample stronger for being
parametric. And `ctx.remove` needs its `In`-proof explicit
(`@ctx.remove _ (wctx w) b bIn`) or `cbn` stalls on an unresolved evar.

For the `safe`/`psafe` semantics these modalities feed into — including
`safe (assume_vareq x t k) ι` being a *guarded implication* whose guard is
exactly fibre-inhabitedness — see `Propositions.v:329` (`safe`), `:2421`
(`psafe`) and `:2455` (`psafe_safe`, which lets you move between them freely).
