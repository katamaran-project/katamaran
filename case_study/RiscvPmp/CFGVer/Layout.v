(* ========================================================================= *)
(* Layout.v — the statement FRONT-END for data memory (PLAN-spec-layer D25). *)
(*                                                                           *)
(* Noninterference.v is the kernel: noninterferent_strong over a mem_layout  *)
(* (blocks at explicit addresses + a disjointness proof).  This file is the  *)
(* user interface on top of it: a program's data written as REGIONS placed   *)
(* back to back (D14), turned into a mem_layout by `compile`, which proves   *)
(* the disjointness once, by shape.  Statements write `compile` explicitly   *)
(* (D16), so this file is on the statement-reading surface: an auditor reads *)
(* `compile` to know what a region list means.  It is not the kernel — a     *)
(* layout `compile` cannot express is written in the kernel's own terms.     *)
(* Requires only the kernel; keep it free of the verifier and of Iris.       *)
(* ========================================================================= *)

From Coq Require Import
     ZArith.ZArith
     Lists.List
     micromega.Lia.
From Katamaran Require Import
     Notations
     Bitvector
     Semantics
     RiscvPmp.Machine
     RiscvPmp.CFGVer.Noninterference.
From stdpp Require Import base vector.

Import RiscvPmpProgram.

Set Implicit Arguments.

(* A region of data, placed right after the previous one (D14).  Arrays and
   byte strings reuse val_spec for their whole contents, with the count
   outside: `Array 4 Secret`, `Array n Public`, `Array 2 (Known [# w0; w1])`. *)
Inductive region : Type :=
| Word  (s : val_spec (Val ty_word))                    (* one word *)
| Array (n : N) (s : val_spec (vec (Val ty_word) (N.to_nat n)))
                                                       (* n consecutive words *)
| Bytes (n : N) (s : val_spec Empty_set)               (* n consecutive bytes *)
| Gap   (n : N).                                       (* n bytes not owned *)
(* Bytes takes only Secret or Public (val_spec Empty_set has no Known): a
   byte string is ROUNDED UP to whole words (D22), and the pad bytes of a
   Known string would have no value.
   TODO (Emiel, D22): look into byte-exact ownership instead of rounding. *)

(* The word specs a region contributes, in address order. *)
Definition region_words (r : region) : list (val_spec (Val ty_word)) :=
  match r with
  | Word s    => [s]
  | Array n s =>
      match s with
      | Secret   => repeat Secret (N.to_nat n)
      | Public   => repeat Public (N.to_nat n)
      | Known ws => List.map Known (vec_to_list ws)
      end
  | Bytes n s =>                                (* D22: rounded up to words *)
      repeat (val_spec_map (fun e : Empty_set => match e with end) s)
             (N.to_nat ((n + 3) / 4))
  | Gap _     => []
  end.

(* Bytes a region occupies: its words, or the gap's length. *)
Definition region_size (r : region) : N :=
  match r with
  | Gap n => n
  | _     => 4 * N.of_nat (length (region_words r))
  end.

Definition layout_size (rs : list region) : N :=
  fold_right (fun r acc => region_size r + acc)%N 0%N rs.

(* Place the regions back to back from address a; a gap only moves on. *)
Fixpoint place (a : N) (rs : list region) : list mem_block :=
  match rs with
  | nil          => nil
  | cons (Gap n) rs => place (a + n) rs
  | cons r rs    =>
      cons {| blk_addr := a; blk_words := region_words r |}
           (place (a + region_size r) rs)
  end.

Lemma place_bounds (a : N) (rs : list region) :
  Forall (fun b => a <= blk_addr b /\ blk_end b <= a + layout_size rs)%N (place a rs).
Proof.
  revert a. induction rs as [|r rs IH]; intros a; [constructor|].
  destruct r as [s|n s|n s|n]; cbn [place layout_size fold_right];
    try (constructor;
         [ unfold blk_end; cbn [blk_addr blk_words region_size]; lia
         | eapply Forall_impl; [apply IH|]; cbn beta; intros b Hb;
           unfold layout_size in Hb; cbn [region_size] in *; lia ]).
  eapply Forall_impl; [apply IH|]; cbn beta; intros b Hb;
    unfold layout_size in Hb; cbn [region_size] in *; lia.
Qed.

Lemma place_disjoint (a : N) (rs : list region) : blocks_disjoint (place a rs).
Proof.
  unfold blocks_disjoint. revert a. induction rs as [|r rs IH]; intros a; [constructor|].
  destruct r as [s|n s|n s|n]; cbn [place];
    [ | | | apply IH ];
    (constructor; [ | apply IH ]);
    (eapply Forall_impl; [ apply place_bounds | ]); cbn beta; intros b Hb;
    left; unfold blk_end in *; cbn [blk_addr blk_words region_size] in *; lia.
Qed.

(* A front-end layout, as the kernel's mem_layout (D16: statements write it). *)
Definition compile (start : N) (rs : list region) : mem_layout :=
  {| blocks := place start rs; blocks_ok := place_disjoint start rs |}.

(* The layout stays inside memory: the statement's own premise (D11). *)
Definition fits (start : N) (rs : list region) : Prop :=
  (start + layout_size rs <= lenAddr)%N.

(* Placed at or after the end of the code, a layout is clear of it (D19). *)
Lemma compile_clear (init_addr : N) (instrs : list AST) (start : N) (rs : list region) :
  (init_addr + 4 * N.of_nat (length instrs) <= start)%N ->
  clear_of_code init_addr instrs (compile start rs).
Proof.
  intros H. unfold clear_of_code, compile. cbn [blocks].
  eapply Forall_impl; [apply place_bounds|]. cbn beta. intros b Hb. right. lia.
Qed.
