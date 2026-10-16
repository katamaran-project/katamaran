(* Tests for the reify_vc tactic of RiscvPmp/Reification.v. *)

From Stdlib Require Import
     Lists.List
     Strings.String
     ZArith.ZArith.
From Katamaran Require Import
     Bitvector
     Context
     Environment
     Syntax.BinOps
     Syntax.TypeDecl
     Syntax.UnOps
     RiscvPmp.Base
     RiscvPmp.Sig
     RiscvPmp.Logic
     RiscvPmp.Reification.
Import RiscvPmpExecutor.
Import Erasure.
Import ListNotations.

From Ltac2 Require Import
     Ltac2
     Printf.

(* Importing Ltac2 makes it the default proof mode again; force Ltac1. *)
Set Default Proof Mode "Classic".

(* Tests: reify_vc succeeds iff the reflected Prop is convertible to the
   goal, and the variables keep (freshened) names. *)
Ltac2 has_hyps (ids : ident list) : unit :=
  List.iter (fun i => let _ := Control.hyp i in ()) ids.

(* Constr.equal ensures syntactic equality (not just convertibility through the `change` tactic) *)
Ltac2 goal_is (c : constr) : unit :=
  if Constr.equal (Control.goal ()) c then ()
  else Control.throw (Tactic_failure (Some (fprintf "expected '%t' but the goal is '%t'" c (Control.goal ())))).

Goal VerificationConditionWithErasure
  (edemonicv (MkB "y" ty.bool)
     (eassumek (eformula_bool (@eterm_var "y" ty.bool 0)) eblock)).
Proof. reify_vc. intros. ltac2:(has_hyps [@y]). Abort.

(* "y.1" is not an identifier; the suffix is dropped. *)
Goal VerificationConditionWithErasure
  (eangelicv (MkB "y.1" ty.bool)
     (eassertk (eformula_bool (@eterm_var "y.1" ty.bool 0)) eblock)).
Proof. reify_vc. intros. ltac2:(has_hyps []). Abort.

Goal VerificationConditionWithErasure
  (edemonicv (MkB "z" ty.bool) (edemonicv (MkB "y" ty.bool)
     (eassume_vareq "z" 1 (@eterm_var "y" ty.bool 0) eblock))).
Proof. reify_vc. intros. ltac2:(has_hyps [@z; @y]). Abort.

(* Invalid or reserved names are still accepted. *)
Goal VerificationConditionWithErasure
  (edemonic_binary eblock
     (eangelicv (MkB "1x" ty.bool) (eangelicv (MkB "fun" ty.bool) eblock))).
Proof. reify_vc. Abort.

Goal VerificationConditionWithErasure
  (edemonicv (MkB "a" ty.bool)
     (eassumek
        (eformula_bool
           (eterm_binop bop.or
              (eterm_unop uop.not (@eterm_var "a" ty.bool 0))
              (eterm_val ty.bool true)))
        eblock)).
Proof. reify_vc. intros. ltac2:(has_hyps [@a]). Abort.

(* Clashing names are freshened: "L", "L.1" and "L.2" all start from L. *)
Goal VerificationConditionWithErasure
  (edemonicv (MkB "L" ty.bool) (edemonicv (MkB "L.1" ty.bool)
     (edemonicv (MkB "L.2" ty.bool)
        (eassumek
           (eformula_bool
              (eterm_binop bop.or
                 (@eterm_var "L" ty.bool 2) (@eterm_var "L.2" ty.bool 0)))
           eblock)))).
Proof. reify_vc. intros. ltac2:(has_hyps [@L; @L1]). Abort.

Goal VerificationConditionWithErasure
  (eassumek
     (eformula_bool
        (eterm_binop bop.and (eterm_val ty.bool true) (eterm_val ty.bool false)))
     eblock).
Proof. reify_vc. ltac2:(goal_is constr:(false = true -> True)). Abort.

Goal VerificationConditionWithErasure
  (eassumek
     (eformula_bool (eterm_unop uop.not (eterm_val ty.bool true)))
     eblock).
Proof. reify_vc. ltac2:(goal_is constr:(false = true -> True)). Abort.

(* Nested constant expressions are folded completely. *)
Goal VerificationConditionWithErasure
  (eassumek
     (eformula_bool
        (eterm_binop bop.or
           (eterm_unop uop.not (eterm_val ty.bool false))
           (eterm_binop bop.and (eterm_val ty.bool false) (eterm_val ty.bool true))))
     eblock).
Proof. reify_vc. ltac2:(goal_is constr:(true = true -> True)). Abort.

(* Integer operators are folded too; the relation is unfolded but not computed. *)
Goal VerificationConditionWithErasure
  (eassumek
     (eformula_relop bop.eq
        (eterm_binop bop.plus (eterm_val ty.int 1%Z) (eterm_val ty.int 2%Z))
        (eterm_val ty.int 3%Z))
     eblock).
Proof. reify_vc. ltac2:(goal_is constr:(@eq (Val ty.int) 3%Z 3%Z -> True)). Abort.

(* Operators with a variable argument are kept, but constant subterms
   below them are folded. *)
Goal VerificationConditionWithErasure
  (edemonicv (MkB "y" ty.bool)
     (eassumek
        (eformula_bool (eterm_binop bop.and (@eterm_var "y" ty.bool 0) (eterm_val ty.bool true)))
        eblock)).
Proof.
  reify_vc.
  ltac2:(goal_is constr:(forall y : Val ty.bool, andb y true = true -> True)).
Abort.

Goal VerificationConditionWithErasure
  (edemonicv (MkB "y" ty.bool)
     (eassumek
        (eformula_bool
           (eterm_binop bop.and
              (eterm_binop bop.and (eterm_val ty.bool true) (eterm_val ty.bool false))
              (@eterm_var "y" ty.bool 0)))
        eblock)).
Proof.
  reify_vc.
  ltac2:(goal_is constr:(forall y : Val ty.bool, andb false y = true -> True)).
Abort.

(* Operators and relations applied to variables are unfolded to the functions
   and relations they denote. *)
Goal VerificationConditionWithErasure
  (edemonicv (MkB "x" ty.int) (edemonicv (MkB "y" ty.int)
     (eassumek
        (eformula_relop bop.lt
           (eterm_binop bop.plus (@eterm_var "x" ty.int 1) (@eterm_var "y" ty.int 0))
           (eterm_val ty.int 10%Z))
        eblock))).
Proof.
  reify_vc.
  ltac2:(goal_is constr:(forall (x y : Val ty.int), (Z.add x y < 10)%Z -> True)).
Abort.

Goal VerificationConditionWithErasure
  (edemonicv (MkB "x" ty.int) (edemonicv (MkB "y" ty.int)
     (eassumek
        (eformula_relop bop.eq (@eterm_var "x" ty.int 1) (@eterm_var "y" ty.int 0))
        eblock))).
Proof.
  reify_vc.
  ltac2:(goal_is constr:(forall (x y : Val ty.int), x = y -> True)).
Abort.

Goal VerificationConditionWithErasure
  (edemonicv (MkB "y" ty.bool)
     (eassumek
        (eformula_bool (eterm_unop uop.not (@eterm_var "y" ty.bool 0)))
        eblock)).
Proof.
  reify_vc.
  ltac2:(goal_is constr:(forall y : Val ty.bool, negb y = true -> True)).
Abort.

(* Signed comparisons become comparisons of [bv.signed] on Z. *)
Goal VerificationConditionWithErasure
  (edemonicv (MkB "x" (ty.bvec 8)) (edemonicv (MkB "y" (ty.bvec 8))
     (eassumek
        (eformula_relop bop.bvslt (@eterm_var "x" (ty.bvec 8) 1) (@eterm_var "y" (ty.bvec 8) 0))
        eblock))).
Proof.
  reify_vc.
  ltac2:(goal_is constr:(forall (x y : Val (ty.bvec 8)), (bv.signed x < bv.signed y)%Z -> True)).
Abort.
