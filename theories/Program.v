(******************************************************************************)
(* Copyright (c) 2019 Dominique Devriese, Georgy Lukyanov,                    *)
(*   Sander Huyghebaert, Steven Keuchel                                       *)
(* All rights reserved.                                                       *)
(*                                                                            *)
(* Redistribution and use in source and binary forms, with or without         *)
(* modification, are permitted provided that the following conditions are     *)
(* met:                                                                       *)
(*                                                                            *)
(* 1. Redistributions of source code must retain the above copyright notice,  *)
(*    this list of conditions and the following disclaimer.                   *)
(*                                                                            *)
(* 2. Redistributions in binary form must reproduce the above copyright       *)
(*    notice, this list of conditions and the following disclaimer in the     *)
(*    documentation and/or other materials provided with the distribution.    *)
(*                                                                            *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS        *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED  *)
(* TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR *)
(* PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR          *)
(* CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,      *)
(* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,        *)
(* PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR         *)
(* PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF     *)
(* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING       *)
(* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS         *)
(* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.               *)
(******************************************************************************)

From Katamaran Require Export
     Syntax.FunDecl
     Syntax.FunDef
     Syntax.Statements
     Base.

Module Type FunDeclMixin (B : Base) :=
  StatementsOn B.

Module Type ProgramMixin (B : Base)
  (Import FDecl : FunDecl B)
  (Import FDK : FunDefKit B FDecl).

  Section InvokedByStm.
    Variable invoke_call : forall {Δ τ1 τ2 Γ}, 𝑭 Δ τ1 -> Stm Γ τ2 -> Prop.

    Fixpoint InvokedByStm_aux {Δ τ1 τ2 Γ} (f : 𝑭 Δ τ1) (s : Stm Γ τ2) : Prop :=
      match s with
      | stm_val _ v => False
      | stm_exp e => False
      | stm_let x σ s1 s2 => InvokedByStm_aux f s1 \/ InvokedByStm_aux f s2
      | stm_block δ s => InvokedByStm_aux f s
      | stm_assign xInΓ s => InvokedByStm_aux f s
      | stm_call f2 es => existT _ (existT _ f) = existT _ (existT _ f2)
                          \/ invoke_call f (FunDef f2)
      | stm_call_frame δ s => InvokedByStm_aux f s
      | stm_foreign f es => False
      | stm_lemmak l es k => InvokedByStm_aux f k
      | stm_seq s k => InvokedByStm_aux f s \/ InvokedByStm_aux f k
      | stm_assertk e1 e2 k => InvokedByStm_aux f k
      | stm_fail _ s => False
      | stm_pattern_match s pat rhs => InvokedByStm_aux f s \/ (exists pc, InvokedByStm_aux f (rhs pc))
      | stm_read_register reg => False
      | stm_write_register reg e => False
      | stm_bind s k => InvokedByStm_aux f s \/ (exists v, InvokedByStm_aux f (k v))
      | stm_debugk k => InvokedByStm_aux f k
      end.
  End InvokedByStm.

  Fixpoint InvokedByStmWithFuel (fuel : nat) {Δ τ1 τ2 Γ} (f : 𝑭 Δ τ1) (s : Stm Γ τ2) : Prop :=
    match fuel with
    (* | 0 => False *)
    | 0 => InvokedByStm_aux (fun _ _ _ _ _ _ => False) f s
    | S fuel => InvokedByStm_aux (@InvokedByStmWithFuel fuel) f s
    end.

  Lemma InvokedByStmWithFuel_S_fuel : forall (fuel : nat) {Δ τ1 τ2 Γ} (f : 𝑭 Δ τ1) (s : Stm Γ τ2),
    InvokedByStmWithFuel fuel f s ->
    InvokedByStmWithFuel (S fuel) f s.
  Proof.
    intros fuel. induction fuel;
      intros Δ τ1 τ2 Γ f s Hinvok.
    - induction s; cbn in *; auto.
      + destruct Hinvok.
        * left. now apply IHs1.
        * right. now apply IHs2.
      + destruct Hinvok; auto. contradiction.
      + destruct Hinvok.
        * left. now apply IHs1.
        * right. now apply IHs2.
      + destruct Hinvok as [Hinvok|Hinvok].
        * left. now apply IHs.
        * right. destruct Hinvok as [pc Hinvok].
          exists pc. now apply H.
      + destruct Hinvok as [Hinvok|Hinvok].
        * left. now apply IHs.
        * right. destruct Hinvok as [v Hinvok].
          exists v. now apply H.
    - induction s; cbn in *; auto.
      + destruct Hinvok.
        * left. now apply IHs1.
        * right. now apply IHs2.
      + destruct Hinvok; auto.
      + destruct Hinvok.
        * left. now apply IHs1.
        * right. now apply IHs2.
      + destruct Hinvok as [Hinvok|Hinvok].
        * left. now apply IHs.
        * right. destruct Hinvok as [pc Hinvok].
          exists pc. now apply H.
      + destruct Hinvok as [Hinvok|Hinvok].
        * left. now apply IHs.
        * right. destruct Hinvok as [v Hinvok].
          exists v. now apply H.
  Qed.

  Definition InvokedByStm {Δ τ1 τ2 Γ} (f : 𝑭 Δ τ1) (s : Stm Γ τ2) : Prop :=
    InvokedByStmWithFuel 2 f s.

  Definition InvokedByFun (fuel : nat) {Δ1 τ1} {Δ2 τ2} (f1 : 𝑭 Δ1 τ1) (f2 : 𝑭 Δ2 τ2) :=
    (* existT _ (existT _ f1) <> existT _ (existT _ f2) /\ *)
    InvokedByStmWithFuel fuel f1 (FunDef f2).

  Definition InvokedByFun_S_fuel : forall (fuel : nat) {Δ1 τ1} {Δ2 τ2} (f1 : 𝑭 Δ1 τ1) (f2 : 𝑭 Δ2 τ2),
    InvokedByFun fuel f1 f2 ->
    InvokedByFun (S fuel) f1 f2.
  Proof.
    intros fuel Δ1 τ1 Δ2 τ2 f1 f2.
    unfold InvokedByFun.
    apply InvokedByStmWithFuel_S_fuel.
  Qed.

  Definition InvokedByFunPackage (fuel : nat) (f1 f2 : {Δ & {τ & 𝑭 Δ τ}}) :=
    match f1, f2 with
    | existT Δ1 (existT τ1 f1) ,  existT Δ2 (existT τ2 f2) => InvokedByFun fuel f1 f2
    end.

  Lemma InvokedByFunPackage_S_fuel : forall (fuel : nat) (f1 f2 : {Δ & {τ & 𝑭 Δ τ}}),
    InvokedByFunPackage fuel f1 f2 ->
    InvokedByFunPackage (S fuel) f1 f2.
  Proof.
    intros fuel [Δ1 [τ1 f1]] [Δ2 [τ2 f2]].
    unfold InvokedByFunPackage.
    apply InvokedByFun_S_fuel.
  Qed.

  Lemma wf_InvokedByFunPackage_S_fuel : forall (fuel : nat) (f : {Δ & {τ & 𝑭 Δ τ}}),
      Wf.Acc (InvokedByFunPackage (S fuel)) f ->
      Wf.Acc (InvokedByFunPackage fuel) f.
  Proof.
    intros fuel f Hacc.
    apply (well_founded.Acc_impl _ _ _ Hacc).
    intros [Δ1 [τ1 f1]] [Δ2 [τ2 f2]] Hinvok.
    now apply InvokedByFunPackage_S_fuel.
  Qed.
End ProgramMixin.

Module Type Program (B : Base) :=
  FunDeclKit B <+ FunDeclMixin B <+ FunDefKit B <+ ProgramMixin B.
