# PLAN-spec-layer — Phase 0 statement drafts (before / after)

Status: rev 3, 2026-10-09 — rev 2 was signed off as readable (Phase 0 exit
criterion); rev 3 only applies the later decisions D15 (`gpr` keys), D16
(`compile` written out, no wrapper), D23 (exit = `ia + 4 * length instrs`)
and the §2a names (`val_spec`, `mem_block`, `mem_layout`) of
`PLAN-spec-layer.md`. Applies D10 (parametric `val_spec`), D11 (proof-carrying base),
D12 (shallow statements) and D14 (region layout, code separate). Anything not
decided is marked (P). Names are placeholders; nothing here compiles yet.
rev 1 (gaps per run, `run_at` derived addresses) was REJECTED: it hid the
addresses.

## 1. Vocabulary

**Values of a single word / register (D10):**

```coq
Inductive val_spec (V : Type) := Secret | Public | Known (v : V).
(* Secret: unconstrained, may differ between the two runs
   Public: equal in both runs, value unknown
   Known v: exactly v in both runs                                   *)
```

**Front-end data layout (D14):** a list of regions, placed back to back
starting at the END OF THE CODE. A gap is a region of its own.

```coq
Inductive region :=                               (* arrays reuse `val_spec` (D14): *)
| Word  (s : val_spec word)                       (* count outside, length by `vec` *)
| Array (n : N) (s : val_spec (vec word n))       (* n consecutive words            *)
| Bytes (n : N) (s : val_spec (vec byte n))       (* n consecutive bytes            *)
| Gap   (n : N).                                   (* n bytes the program does not own *)
```

**Trusted statement (the kernel, `Noninterference.v`):** unchanged in shape —
load address, instructions (`mem_has_instrs`, D14: code stays separate),
exit address, registers — but register keys are `gpr` (x1–x31, D15) and
memory is a `mem_layout` (D11): `mem_block`s at explicit addresses plus a
disjointness proof, clear of the code by a conjunct of `noninterferent_strong`
(D19). A front-end layout gets there through `compile` (in `Layout.v`,
D25), which proves disjointness once, by shape. Statements write `compile`
explicitly (D16):

```coq
Definition fits (start : N) (data : list region) : Prop := start + size data <= lenAddr.
(* every statement below:
   fits … -> noninterferent_strong ia code (ia + 4 * length code) regs
                                   (compile (ia + 4 * length code) data)  *)
```

## 2. cmovznz4

**Before** (`Cmovznz4Result.v:57–62`, `Cmovznz4.v:179–193`):

```coq
Lemma cmovznz4_noninterferent_param (init_addr : N) :
  (init_addr + 164 < lenAddr)%N ->
  noninterferent_strong init_addr cmovznz4_instrs (init_addr + 116)%N
    (map (concretize_reg init_addr) cmovznz4_reg_specs_rel)
    (map (concretize_mem init_addr) cmovznz4_mem_specs_rel).

cmovznz4_reg_specs_rel :=
  [(A0, false, PVExist); (A1, false, PVBaseOff 116); (A2, false, PVBaseOff 132);
   (A3, false, PVBaseOff 148); (A4, false, PVExist); … (T1, false, PVExist)].
cmovznz4_mem_specs_rel :=
  [(116%N, false, PVExist); (120%N, false, PVExist); … 12 entries … (160%N, false, PVExist)].
```

Traps: A1–A3 read "secret" but are public; `+164` is unexplained; two
`concretize_*` maps.

**After:**

```coq
(* code: ia .. ia+115 (29 instructions) *)
Definition cmovznz4_data : list region :=
  [ Array 4 Secret        (* x[0..3]  at ia+116 *)
  ; Array 4 Secret        (* y[0..3]  at ia+132 *)
  ; Array 4 Secret ].     (* r[0..3]  at ia+148 *)

Definition cmovznz4_regs (ia : N) :=
  [ (A0, Secret);                                        (* cin *)
    (A1, Known (bv.of_N (ia + 116)));                    (* &x  *)
    (A2, Known (bv.of_N (ia + 132)));                    (* &y  *)
    (A3, Known (bv.of_N (ia + 148)));                    (* &r  *)
    (A4, Secret); (A5, Secret); (A6, Secret); (A7, Secret); (T0, Secret); (T1, Secret) ].

Theorem cmovznz4_noninterferent (ia : N) :
  fits (ia + 4 * length cmovznz4_instrs) cmovznz4_data ->
  noninterferent_strong ia cmovznz4_instrs (ia + 4 * length cmovznz4_instrs) (cmovznz4_regs ia)
    (compile (ia + 4 * length cmovznz4_instrs) cmovznz4_data).
```

## 3. muladd (BearSSL `br_i31_muladd_small`, every header b)

**Before** (`MuladdParamResult.v:291–302` + end theorem; `MuladdParam.v:42–77`):

```coq
Lemma muladd_param_noninterferent (init_addr : N) (b : bv xlenbits) :
  (64 < bv.unsigned b < 65536)%Z ->
  (init_addr + 1128 + 4 * N.of_nat (2 * mlenN b + 6) < lenAddr)%N ->
  noninterferent_strong init_addr sym6_instrs (init_addr + 1128)%N
    (sym_reg_specs init_addr b) (sym_mem_specs init_addr b).

sym_reg_specs ia b := (A0, true, Some (bv.of_N (ia + x_off b))) :: map (concretize_reg ia) sym_regs.
sym_mem_specs ia b := concretize_data (sym_ι ia b) (ia + 1128) sym_data.
sym_ι ia b := [env].["p" ↦ SyncVal (bv.of_N ia)].["b" ↦ SyncVal b]
                   .["x" ↦ SyncVal (bv.of_N (ia + x_off b))].["a" ↦ SyncVal (bv.of_N ia)].
sym_data := [ DCell false None ×4; DCell true (Some (term_var "b"));
              DArr true ArrUp (t_mm2 (term_var "b")); DCell true None ×2;
              DAt (term_var "x"); DCell true (Some (term_var "b"));
              DArr false ArrDown (t_mm2 (term_var "b")); DCell false None ×2 ].
```

Traps: Terms + valuation + `rv_val`; `DAt`/`ArrUp`/`ArrDown` mean nothing
in the statement; x's address stated three times; literal `+1128`; A0
consed on by hand.

**After:**

```coq
Definition M (b : bv xlenbits) : N := (bv.bin b + 31) / 32.     (* limb count *)

(* code: ia .. ia+1127 (282 instructions) *)
Definition muladd_data (b : bv xlenbits) : list region :=
  [ Array 4 Secret                            (* S0–S3 spill slots, ia+1128   *)
  ; Word (Known b) ; Array (M b) Public       (* m = sp, ia+1144: header, limbs *)
  ; Word (Known b) ; Array (M b) Secret ].    (* x, ia+1148+4·M: header, limbs *)

Definition muladd_regs (ia : N) (b : bv xlenbits) :=
  [ (A0, Known (bv.of_N (ia + 1148 + 4 * M b)));    (* &x[0]       *)
    (A1, Secret);                                   (* z           *)
    (A2, Known (bv.of_N (ia + 1144)));              (* &m[0]       *)
    (X2, Known (bv.of_N (ia + 1144)));              (* sp          *)
    (A3, Secret); … (T6, Secret); (S0, Secret); … (S3, Secret) ].

Theorem muladd_noninterferent (ia : N) (b : bv xlenbits) :
  (64 < bv.unsigned b < 65536)%Z ->
  fits (ia + 4 * length muladd_instrs) (muladd_data b) ->
  noninterferent_strong ia muladd_instrs (ia + 4 * length muladd_instrs) (muladd_regs ia b)
    (compile (ia + 4 * length muladd_instrs) (muladd_data b)).
```

m and x are now "header + M limbs". The old split into `M − 2` limbs plus
two top cells was a proof need (the code reads the top limbs individually)
and stays in the contract, like `dir` and `DAt`. The b-range premise is the
PROOF's (the code's own branches); the layout is disjoint for every b. Exit:
group B's `+1128` literal becomes `4 * length muladd_instrs`.

## 4. check_scalar with k a pointer argument

**Before** (`CheckScalarPtrResult.v:80–94`, `CheckScalarPtr.v:14–23`):

```coq
Lemma check_scalar_ptr_noninterferent (init_addr ka : N) (l : bv xlenbits) :
  (init_addr + 176 < lenAddr)%N ->
  (ka + 4 * N.of_nat (klen_words l) < lenAddr)%N ->
  (ka + 4 * N.of_nat (klen_words l) <= init_addr \/ init_addr + 176 <= ka)%N ->
  noninterferent_strong init_addr cs_instrs (init_addr + 4 * N.of_nat (length cs_instrs))%N
    (map (concretize_reg_q (csp_ι init_addr ka l)) csp_regs)
    (concretize_data (csp_ι init_addr ka l).["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)]
       (init_addr + 144) csp_data).

csp_regs := [ (A0, true, PVVar "k"); (A1, true, PVVar "l"); (X1, true, PVOff "p" 144);
              (A2, false, PQExist); … (A7, false, PQExist) ].
csp_data := [ DBytes false 32; DPtr (term_var "k"); DBytes false (term_var "l") ].
```

**After, front-end (k above P256_N, g bytes further):**

```coq
(* code: ia .. ia+143 (36 instructions) *)
Definition cs_data (g : N) (l : bv xlenbits) : list region :=
  [ Bytes 32 Secret             (* P256_N, ia+144 (unpinned: stronger) *)
  ; Gap g
  ; Bytes (bv.bin l) Secret ].  (* k[0 .. l-1], ia+176+g                 *)

Definition cs_regs (ia g : N) (l : bv xlenbits) :=
  [ (A0, Known (bv.of_N (ia + 176 + g)));     (* k     *)
    (A1, Known l);                            (* klen  *)
    (X1, Known (bv.of_N (ia + 144)));         (* ra = the exit *)
    (A2, Secret); … (A7, Secret) ].

Theorem check_scalar_noninterferent (ia g : N) (l : bv xlenbits) :
  fits (ia + 4 * length cs_instrs) (cs_data g l) ->
  noninterferent_strong ia cs_instrs (ia + 4 * length cs_instrs) (cs_regs ia g l)
    (compile (ia + 4 * length cs_instrs) (cs_data g l)).
```

**After, base (k anywhere, either side of the code):** the front-end
cannot place data below the code, so this one is written in the D11 base
directly; the parameter premise feeds the disjointness proof (D11):

```coq
Definition cs_mem (ia ka : N) (l : bv xlenbits)
    (H : ka + 4 * klen_words l <= ia \/ ia + 176 <= ka) : mem_layout :=
  {| blocks := [ {| blk_addr := ia + 144; blk_words := repeat Secret 8 |}               (* P256_N *)
               ; {| blk_addr := ka;       blk_words := repeat Secret (klen_words l) |} ] (* k *)
   ; blocks_ok := cs_disjoint ia ka l H |}.

Theorem check_scalar_anywhere_noninterferent (ia ka : N) (l : bv xlenbits)
    (H : ka + 4 * klen_words l <= ia \/ ia + 176 <= ka) :
  ia + 176 < lenAddr -> ka + 4 * klen_words l < lenAddr ->
  noninterferent_strong ia cs_instrs (ia + 4 * length cs_instrs) (cs_regs' ia ka l) (cs_mem ia ka l H).
```

## 5. Open points raised by the drafts

1. RESOLVED (D14): arrays reuse `val_spec` via `vec`, no second constructor set.
2. Each Result proves "shallow data = the generator's deep specs" (D12) —
   as the two `≡ₚ` premises of the bridge (`PLAN-spec-layer.md` §2a.5);
   priced at the end of Phase 3.
3. RESOLVED for now (D22): `Bytes` rounds up to whole words; TODO on
   byte-exact ownership. Knock-on (§2a.2 P1, proposal): `Bytes` takes only
   `Secret | Public` meanwhile.
4. RESOLVED (D15, P2): keys are `gpr`, a subset of `Reg ty_xlenbits`.
5. RESOLVED (D16): no wrapper; `compile` is written out.
6. Register addresses are literal (`ia + 1148 + 4 * M b`) and must agree
   with the layout; a mismatch makes the theorem unprovable (not unsound).
