---
name: relval-model
description: >
  Katamaran's relational value representation: RelVal = RV (Val σ) =
  SyncVal (agrees on both executions / public) | NonSyncVal (may differ /
  secret), how unops/binops lift homomorphically over the pair
  (liftUnOpRV / liftBinOpRV / evalRel), and why NonSyncVal is contagious but
  never crashes at the value level. Read this to understand what a term denotes
  in the binary/relational (noninterference) executor, whenever SyncVal or
  NonSyncVal shows up in a goal or definition, or before working with the two
  same-named RelVal definitions (TypeDecl.v vs ShallowExecutorRel.v). Foundational
  reference; pairs with `relval-rewrite-over-secrets` (rewrite soundness over
  secrets) and `secret-data-walls` (the NonSyncVal ⇒ False boundary).
  Framework-wide (theories/), not CFGVer-specific; a library skill.
---

# Relational value model (SyncVal / NonSyncVal)

The binary/relational verifier evaluates every program **twice** (a "left" and a
"right" execution) to prove noninterference. A value is therefore a
*pair-or-single*:

```coq
Inductive RV (A : Type) := SyncVal : A -> RV A | NonSyncVal : A -> A -> RV A.   (* TypeDecl.v:157 *)
Definition RelVal σ := RV (Val σ).                                              (* TypeDecl.v:189 *)
```

- **`SyncVal v`** — both executions hold the same `v`. Morally *public / low*: an
  attacker observing it learns nothing that distinguishes the runs.
- **`NonSyncVal vl vr`** — the executions may differ (`vl` left, `vr` right).
  Morally *secret / high*.

`projLeftRV` / `projRightRV` (TypeDecl.v:175-187) read one side (`SyncVal v`
projects to `v` on both).

> **Two RelVals, same constructor names.** The term-level one is `RV (Val σ)` in
> `theories/Syntax/TypeDecl.v`. There is a *separate* standalone
> `Inductive RelVal` with the same `SyncVal`/`NonSyncVal` constructors in
> `theories/Staging/BinaryExecutor/ShallowExecutorRel.v:73-75`. Term denotation
> (`inst`) uses the `TypeDecl` one.

## Operations lift homomorphically — secrets never crash at the value level

Every unop/binop is lifted pointwise over the pair:

```coq
liftUnOpRV  f rv  = match rv with SyncVal v => SyncVal (f v) | NonSyncVal l r => NonSyncVal (f l) (f r) end.  (* TypeDecl.v:212 *)
liftBinOpRV f rv1 rv2 =
  match (rv1,rv2) with
  | (SyncVal v1, SyncVal v2) => SyncVal (f v1 v2)
  | (_,_) => NonSyncVal (f (projLeftRV rv1) (projLeftRV rv2)) (f (projRightRV rv1) (projRightRV rv2))  (* TypeDecl.v:255 *)
  end.
evalRel op = liftBinOp (eval op).   (* BinOps.v:411 — eval is the plain Val-level op, BinOps.v:385 *)
```

Consequences worth internalizing:

- **`NonSyncVal` is contagious**: any op with a `NonSyncVal` operand yields a
  `NonSyncVal` result, computed independently on each side. A term built over
  secret inputs denotes a `NonSyncVal` — it does **not** error or get stuck. So
  arbitrary arithmetic on secrets is fine *as values*.
- **Projection commutes with ops**:
  `projLeft (liftBinOp f a b) = f (projLeft a) (projLeft b)` (TypeDecl.v:372, plus
  the `projRight` twin) — each side is just the ordinary Val-level computation.

These two facts are the root of the other two skills:
- that a pure-term rewrite proved as a plain `Val`/`bv` identity is automatically
  sound over secrets → **`relval-rewrite-over-secrets`**;
- that secrets are nonetheless forbidden from being *observed* (secret data ⇒
  `False` in any formula / `secLeak`) → **`secret-data-walls`**.
