# PLAN-spec-layer — Phase 0 statement drafts (before / after)

Status: DRAFT 2026-10-09, for Emiel's readability sign-off (PLAN-spec-layer
Phase 0 exit criterion). Applies D10 (parametric spec), D11 (proof-carrying
layout + shape-B front-end) and Q1b = SHALLOW (plain Coq data + a proved
correspondence to the generator's deep specs). Everything not in D1–D11 is a
PROPOSAL, marked (P). Names are placeholders. Nothing here compiles yet.

## 1. Trusted vocabulary (sketch, `Noninterference.v`)

```coq
Inductive spec (V : Type) := Secret | Public | Known (v : V).        (* D10 *)
Inductive vis := VSecret | VPublic.        (* arrays: no Known — Q1a open (P) *)

Inductive item :=                                   (* one contiguous run *)
| Word  (s : spec (bv 32))                          (* 1 word              *)
| Words (n : N) (v : vis)                           (* n words             *)
| Bytes (n : N) (v : vis).                          (* n bytes, word-padded *)

Record program := {                                  (* D11, code bundled (P) *)
  load_at : N;  code : list AST;
  data    : list (N * list item);                    (* absolute start, run  *)
  wf      : layout_ok load_at code data }.           (* Prop: code + runs
                                                        pairwise disjoint, N *)
Definition code_end P := load_at P + 4 * length (code P).
Definition fits P : Prop := (* every run ends below lenAddr *) …
Definition run_at P i : bv xlenbits := (* start of data run i *) …

Definition noninterferent_strong
  (P : program) (exit_addr : N) (regs : list (RegKey * spec (bv xlenbits)))
  : Prop := …        (* RegKey: Q2 open *)
```

Shape-B builder (front-end, NOT trusted, proved once) (P):

```coq
(* runs packed after the code, each after the previous one + its gap *)
Definition program_of (ia : N) (c : list AST) (rs : list (N * list item)) : program
  := {| load_at := ia; code := c; data := place (ia + 4 * length c) rs;
        wf := place_ok ia c rs |}.       (* place_ok: by shape, NO hypotheses *)
```

## 2. cmovznz4

**Before** (`Cmovznz4Result.v:57–62` + `Cmovznz4.v:179–193`):

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
  [(116%N, false, PVExist); (120%N, false, PVExist); … 12 entries … (160%N, …)].
```

Reader traps: A1–A3 read "secret" but are public; `+116` and `+164` are
unexplained literals; two `concretize_*` maps to understand.

**After:**

```coq
Definition cmovznz4_prog (ia : N) : program :=
  program_of ia cmovznz4_instrs
    [ (0, [Words 4 VSecret])                   (* x *)
    ; (0, [Words 4 VSecret])                   (* y *)
    ; (0, [Words 4 VSecret]) ].                (* r *)

Definition cmovznz4_regs (ia : N) :=
  let P := cmovznz4_prog ia in
  [ (A0, Secret);                                         (* cin *)
    (A1, Known (run_at P 0)); (A2, Known (run_at P 1)); (A3, Known (run_at P 2));
    (A4, Secret); (A5, Secret); (A6, Secret); (A7, Secret); (T0, Secret); (T1, Secret) ].

Theorem cmovznz4_noninterferent (ia : N) :
  fits (cmovznz4_prog ia) ->
  noninterferent_strong (cmovznz4_prog ia) (code_end (cmovznz4_prog ia)) (cmovznz4_regs ia).
```

## 3. muladd (BearSSL `br_i31_muladd_small`, every header b)

**Before** (`MuladdParamResult.v:291–302`, end theorem; `MuladdParam.v:42–77`):

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

Reader traps: Terms + valuation + `rv_val`; `DAt`/`ArrUp`/`ArrDown` mean
nothing in the statement; x's address stated three times; literal `+1128`;
A0 consed on by hand.

**After:**

```coq
Definition M (b : bv xlenbits) : N := (bv.bin b + 31) / 32.   (* limb count *)

Definition muladd_prog (ia : N) (b : bv xlenbits) : program :=
  program_of ia muladd_instrs
    [ (0, [Word Secret; Word Secret; Word Secret; Word Secret])   (* S0–S3 spills *)
    ; (0, [Word (Known b); Words (M b - 2) VPublic;               (* m: header b, *)
           Word Public; Word Public])                             (*   M limbs    *)
    ; (0, [Word (Known b); Words (M b - 2) VSecret;               (* x: header b, *)
           Word Secret; Word Secret]) ].                          (*   M limbs    *)

Definition muladd_regs (ia : N) (b : bv xlenbits) :=
  let P := muladd_prog ia b in
  [ (A0, Known (run_at P 2));                  (* &x[0] *)
    (A1, Secret);                              (* z     *)
    (A2, Known (run_at P 1)); (X2, Known (run_at P 1));   (* &m[0] = sp *)
    (A3, Secret); … (S3, Secret) ].

Theorem muladd_noninterferent (ia : N) (b : bv xlenbits) :
  (64 < bv.unsigned b < 65536)%Z ->
  fits (muladd_prog ia b) ->
  noninterferent_strong (muladd_prog ia b) (code_end (muladd_prog ia b)) (muladd_regs ia b).
```

The b-range premise stays: it is what the PROOF needs (the code's own
branches), not disjointness — x's start is DERIVED (`run_at P 2`), so the
layout is disjoint for every b. Written with `x_off b = 1148 + 4M` instead,
it would overlap for M < 2 (`M - 2` truncates in N) and need the premise in
the type. Also fixes group B's literal exit (`code_end`) and the
three-times-stated x.

## 4. check_scalar with k a pointer argument (CheckScalarPtr)

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

**After, order 1 (k above the code and P256_N; its position is a gap g):**

```coq
Definition cs_prog (ia g : N) (l : bv xlenbits) : program :=
  program_of ia cs_instrs
    [ (0, [Bytes 32 VSecret])                  (* P256_N (unpinned: stronger) *)
    ; (g, [Bytes (bv.bin l) VSecret]) ].       (* k[0 .. l-1], g bytes further *)

Definition cs_regs (ia g : N) (l : bv xlenbits) :=
  let P := cs_prog ia g l in
  [ (A0, Known (run_at P 1));                  (* k    *)
    (A1, Known l);                             (* klen *)
    (X1, Known (bv.of_N (code_end P)));        (* ra = the exit *)
    (A2, Secret); … (A7, Secret) ].

Theorem check_scalar_noninterferent (ia g : N) (l : bv xlenbits) :
  fits (cs_prog ia g l) ->
  noninterferent_strong (cs_prog ia g l) (code_end (cs_prog ia g l)) (cs_regs ia g l).
```

Three premises → one; the disjunction disappears into the shape. Order 2
(k BELOW the code) is a second program value and theorem from the same VC
and bridge — but `program_of` puts the code first, so it needs a builder
where the code is any run (P).

## 5. Open points raised by the drafts

1. Bundling the code into `program` (P): one argument instead of
   `init_addr instrs`, and "clear of the code" is part of `wf`.
2. Arrays' spec (`vis`, no `Known`) — the Known-free part of D10; naming.
3. Q2 key type (`RegKey`): `Reg ty_xlenbits` also contains `pc`, `mtvec`,
   `pmpaddr0`… (`Base.v:973–1015`), not only x1–x31.
4. `Bytes` in a word-granular trusted memory (today's statement owns the
   pad bytes of the last word) — interacts with Q3.
5. Each Result needs `prog/regs = translation of the generator's deep specs`;
   with symbolic b/l that equality is a proof (cbn + lia), not vm_compute.
   Risk: per-example proof cost (cf. TODO: muladd's ~75 lines of bv lemmas).
6. Registers mention layout positions (`run_at P i`), so registers and
   memory cannot drift apart; a register pointing INTO a run (m = sp) is why
   muladd's spills are their own run.
