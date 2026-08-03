---
name: rocq-pitfalls
description: >
  Generic Rocq/Coq tactic gotchas observed in this project and NOT covered by the
  rocq plugin (verified 2026-07-16): bullet discipline errors ("Wrong bullet -:
  Current bullet - is not finished"), non-failure-atomic tactic combos (try (eapply
  L; eauto) leaving stray side goals), SSReflect rewrite syntax surprises (comma
  chains, the Ltac "by" clause), the goal-debugging print settings (Unset
  Printing Notations, Set Printing Implicit / All, Set Typeclasses Debug),
  a plain N/Z/nat arithmetic goal unexpectedly type-erroring against Term/Val
  in a file that imports TermNotations/asn.notations (open notations silently
  hijacking +/-/*/=; fix with an explicit %N/%Z scope annotation), and
  `injection H as ->`/`<-` picking the wrong rewrite direction ("Found no
  subterm matching" even though the equation is obviously usable). Use when
  hitting any of those symptoms in any .v file. NOT for Katamaran-, Iris-, gmap-, or
  bv-specific pitfalls (their own skills).
---

# Rocq pitfalls (generic, project-observed)

Sharp-edged generic gotchas the rocq plugin's references don't cover.

## Debugging confusing goals

Paste at the top of the proof state under inspection:

```coq
Unset Printing Notations.    (* see raw terms instead of notation *)
Set Printing Implicit.       (* show implicit arguments *)
Set Printing All.            (* show everything; very verbose *)
Set Typeclasses Debug.       (* trace typeclass search *)
```

Reset with the `Un/Set` inverse. `Print <instance-name>.` inspects a specific
typeclass instance.

## Bullet discipline

`Wrong bullet -: Current bullet - is not finished` — nested case splits must use a
*different* bullet symbol per nesting level. Inside a `-` bullet (e.g. from
`iInduction`), use `+` for the next level, then `--`, then `*`. The error often
appears far from the real cause: a sub-goal silently left open (e.g. a missing
second `iFrame`) makes the *next* bullet look wrong.

## `try (eapply L; eauto)` is not failure-atomic

`eauto` never fails — it succeeds doing nothing. So on a goal whose conclusion
matches `L` but whose side conditions are underivable, the combo COMMITS to
`eapply` and leaves the stray side-condition goals behind, instead of reverting.
Wrap as `try (solve [eapply L; eauto])` to get discharge-or-revert semantics.

## SSReflect `rewrite` syntax (active wherever SSReflect is imported)

- **No comma chains**: `rewrite h1, h2.` is a syntax error
  ("Syntax error: [ltac_use_default] expected"). Chain space-separated:
  `rewrite h1 h2.`
- **No Ltac `by` clause on `rewrite … in H`**: SSReflect's `rewrite` rejects
  `rewrite lem in H by tac.` Provide conditional-lemma side conditions as explicit
  hypotheses instead: `assert (Hs : …) by (…); rewrite (lem Hs) in H.`

Note: importing one SSReflect-using module (e.g. via a dependency) is enough to
switch `rewrite` to SSReflect's grammar in your whole file.

## Open notations hijack plain arithmetic (`TermNotations`/`asn.notations`)

CFGVer files (and others) `Import TermNotations`/`asn.notations` for writing
assertions/terms — these redefine `+`, `-`, `*`, `=`, `<=ᵘ` etc. for `Term`/`Val`.
Writing an ordinary `N`/`Z`/`nat` arithmetic expression (e.g. inside a helper
`Lemma`/`Fixpoint` you're adding to the same file) can silently pick up the
WRONG notation, producing a confusing type error like `The term "x" has type
"N" while it is expected to have type "Term ?Σ ty.int"` at a `+`/`-` that looks
completely innocent. Fix: annotate the whole expression with the intended
scope, e.g. `(a + b)%N`, rather than trying to figure out which `+` Coq picked.

## `rewrite` matches keyed on the head symbol — beta-reduced occurrences don't fire

`rewrite L in H` fails with **"The LHS of L … does not match any subterm of the
goal"** even when the two sides are *definitionally equal*, if `L`'s LHS is
stated with a head symbol that the occurrence in `H` no longer has. The usual
cause in this codebase is a monadic lemma stated via `bind`:

```coq
Lemma L … : (_ <- m ;; k) Φ h = k Φ (f h).   (* LHS head: CHeapSpec.bind *)
```

against a hypothesis a continuation already beta-reduced past the `bind`:

```coq
H : m (fun _ h1 => k Φ h1) h                  (* head: m — no bind left *)
```

`rewrite` does keyed matching on the head, so there is nothing to key on and it
refuses, no matter how many `unfold`/`cbn`s you try on the lemma side. **Fix:
state (or derive) the forward implication and use `apply … in`, which unifies up
to full conversion:**

```coq
Lemma L_fwd … : (_ <- m ;; k) Φ h -> k Φ (f h).
Proof. now rewrite L. Qed.                    (* the goal-side rewrite is fine *)
…
apply L_fwd in H.                              (* succeeds where rewrite failed *)
```

Note the asymmetry: `rewrite L` works fine *inside* `L_fwd`, because there the
LHS is the literal statement, still `bind`-headed. It is only the beta-reduced
*occurrence* that defeats it. Real instance: `cgc_binds_heap` /
`cgc_binds_heap_fwd` in `CFGVer/VerifierRel.v`, consumed by `Adequacy.v`.

Generalisation worth remembering: when a `rewrite` "obviously should" apply and
doesn't, check whether the occurrence's head symbol is the same as the lemma
LHS's — not whether the terms are equal. If they differ, switch to a
conversion-based tactic (`apply … in`, `change`, `exact`) rather than fighting it.

## `injection H as ->`/`<-` picks a rewrite direction — the wrong one silently fails

`injection H as ->` (or `<-`) doesn't just extract the equality from `H : Some x
= Some y` — it immediately `rewrite`s the goal with it in the given direction,
then clears it. `as ->` rewrites left-to-right (replaces occurrences of the
equation's LHS in the goal with its RHS); `as <-` goes the other way. If the
goal is `spec = y` and the extracted equation is `x = spec` (not `spec = x`),
asking for `as ->` tries to find `x` literally in the goal — which isn't there
(the goal has `spec`, not yet substituted) — and fails with "Found no subterm
matching", even though the equation is perfectly usable the other direction.
When in doubt, use `injection H as H` (keep the raw equation) and follow with
`subst` (which finds the right direction automatically since it just needs one
side to be a bare variable) instead of guessing `->` vs `<-`.

## SSReflect's `by` does not run the tactic you wrote (2026-08-01)

With SSReflect in scope (anything importing Iris), `replace X with Y by (tac1;
tac2)` can apply `tac2` to the UNCHANGED goal — the classic symptom is

```coq
replace (f a) with (g a) by (symmetry; apply my_lemma).
(* Unable to unify "g ?x = f ?x" with "f a = g a"  — symmetry never ran *)
```

Use an explicit `assert` + `rewrite` instead, which is unambiguous:

```coq
assert (Hcomm : f a = g a) by ... .   (* or: assert (...). { symmetry. apply my_lemma. } *)
rewrite Hcomm.
```

Related, same cause: SSReflect rejects the comma form `rewrite H1, H2 in H` —
write one rewrite per step, `rewrite H1 in H. rewrite H2 in H.`

## A `rewrite` that will not fire on a term you can SEE in the goal

If `rewrite <- some_lemma` reports *"Found no subterm matching …"* but dumping
the goal (`match goal with |- ?G => idtac "ZZ:" G end`) shows the term verbatim,
the mismatch is in **implicit instance arguments**, not shape — typeclass-driven
functions like `inst` resolve differently in the lemma's statement than in the
goal. Fully instantiating the lemma's explicit arguments does NOT help. Fix:
`assert` the equation you want in the exact form the goal uses, prove it by
`apply`ing the lemma, then `rewrite` the assertion.
