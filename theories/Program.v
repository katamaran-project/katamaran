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

  Definition 𝑭_eqb {Δ1 Δ2 τ1 τ2} (f1 : 𝑭 Δ1 τ1) (f2 : 𝑭 Δ2 τ2) : bool :=
    if @Classes.eq_dec _ 𝑭_eq_dec (existT _ (existT _ f1)) (existT _ (existT _ f2))
    then true
    else false.

  (* TODO: very annoying definition, but otherwise the wrong eq with existT pops up,
           see commented out definition below
           (we get `existT (𝑭 Δ) ...` instead of `existT Δ ...`) *)
  (* Definition wrong {Δ1 Δ2 τ1 τ2} (f1 : 𝑭 Δ1 τ1) (f2 : 𝑭 Δ2 τ2) : Prop :=
    existT _ (existT _ f1) = existT _ (existT _ f2).
  Print wrong. *)
  Definition 𝑭_eq {Δ1 Δ2 τ1 τ2} (f1 : 𝑭 Δ1 τ1) (f2 : 𝑭 Δ2 τ2) : Prop :=
   (@existT (NCtx (@PVar B.varkit) (@Ty B.typedeclkit))
      (fun Γ : NCtx (@PVar B.varkit) (@Ty B.typedeclkit) => {x : @Ty B.typedeclkit & 𝑭 Γ x}) Δ1
      (@existT (@Ty B.typedeclkit) (𝑭 Δ1) τ1 f1)) =
   (@existT (NCtx (@PVar B.varkit) (@Ty B.typedeclkit))
      (fun Γ : NCtx (@PVar B.varkit) (@Ty B.typedeclkit) => {x : @Ty B.typedeclkit & 𝑭 Γ x}) Δ2
      (@existT (@Ty B.typedeclkit) (𝑭 Δ2) τ2 f2)).

  Section InvokedByStm.
    Variable invoke_call : forall {Δ τ1 τ2 Γ}, 𝑭 Δ τ1 -> Stm Γ τ2 -> Prop.

    Fixpoint InvokedByStm_aux {Δ τ1 τ2 Γ} (f : 𝑭 Δ τ1) (s : Stm Γ τ2) : Prop :=
      match s with
      | stm_val _ v => False
      | stm_exp e => False
      | stm_let x σ s1 s2 => InvokedByStm_aux f s1 \/ InvokedByStm_aux f s2
      | stm_block δ s => InvokedByStm_aux f s
      | stm_assign xInΓ s => InvokedByStm_aux f s
      | stm_call f2 es => 𝑭_eq f f2 \/ invoke_call f (FunDef f2)
      | stm_call_frame δ s => InvokedByStm_aux f s
      | stm_foreign f es => False
      | stm_lemmak l es k => InvokedByStm_aux f k
      | stm_seq s k => InvokedByStm_aux f s \/ InvokedByStm_aux f k
      | stm_assertk e1 e2 k => InvokedByStm_aux f k
      | stm_fail _ s => False
      | stm_pattern_match s pat rhs => InvokedByStm_aux f s \/ (exists pc, InvokedByStm_aux f (rhs pc))
      | stm_read_register reg => False
      | stm_write_register reg e => False
      | stm_bind s k => False (* stm_bind should not be used in source code directly, hence we don't include it in the search of fn invocations *)
      | stm_debugk k => InvokedByStm_aux f k
      end.
  End InvokedByStm.

  Section InvokedByStmBool.
    Variable invoke_call : forall {Δ τ1 τ2 Γ}, 𝑭 Δ τ1 -> Stm Γ τ2 -> bool.

    Fixpoint InvokedByStmB_aux {Δ τ1 τ2 Γ} (f : 𝑭 Δ τ1) (s : Stm Γ τ2) : bool :=
      match s with
      | stm_val _ v => false
      | stm_exp e => false
      | stm_let x σ s1 s2 => InvokedByStmB_aux f s1 || InvokedByStmB_aux f s2
      | stm_block δ s => InvokedByStmB_aux f s
      | stm_assign xInΓ s => InvokedByStmB_aux f s
      | stm_call f2 es => 𝑭_eqb f f2 || invoke_call f (FunDef f2)
      | stm_call_frame δ s => InvokedByStmB_aux f s
      | stm_foreign f es => false
      | stm_lemmak l es k => InvokedByStmB_aux f k
      | stm_seq s k => InvokedByStmB_aux f s || InvokedByStmB_aux f k
      | stm_assertk e1 e2 k => InvokedByStmB_aux f k
      | stm_fail _ s => false
      | stm_pattern_match s pat rhs =>
          InvokedByStmB_aux f s
          || List.existsb (fun pc => InvokedByStmB_aux f (rhs pc))
                          (@finite.enum _ _ (B.Finite_PatternCase pat))
      | stm_read_register reg => false
      | stm_write_register reg e => false
      | stm_bind s k => false
      | stm_debugk k => InvokedByStmB_aux f k
      end.
  End InvokedByStmBool.

  Fixpoint InvokedByStmWithFuel (fuel : nat) {Δ τ1 τ2 Γ} (f : 𝑭 Δ τ1) (s : Stm Γ τ2) : Prop :=
    match fuel with
    | 0 => InvokedByStm_aux (fun _ _ _ _ _ _ => False) f s
    | S fuel => InvokedByStm_aux (@InvokedByStmWithFuel fuel) f s
    end.

  Fixpoint InvokedByStmWithFuelBool (fuel : nat) {Δ τ1 τ2 Γ} (f : 𝑭 Δ τ1) (s : Stm Γ τ2) : bool :=
    match fuel with
    | 0 => InvokedByStmB_aux (fun _ _ _ _ _ _ => false) f s
    | S fuel => InvokedByStmB_aux (@InvokedByStmWithFuelBool fuel) f s
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
  Qed.

  Definition InvokedByStm {Δ τ1 τ2 Γ} (f : 𝑭 Δ τ1) (s : Stm Γ τ2) : Prop :=
    InvokedByStmWithFuel 2 f s.

  Definition InvokedByStmBool {Δ τ1 τ2 Γ} (f : 𝑭 Δ τ1) (s : Stm Γ τ2) : bool :=
    InvokedByStmWithFuelBool 2 f s.

  Definition InvokedByFun (fuel : nat) {Δ1 τ1} {Δ2 τ2} (f1 : 𝑭 Δ1 τ1) (f2 : 𝑭 Δ2 τ2) : Prop :=
    InvokedByStmWithFuel fuel f1 (FunDef f2).

  Definition InvokedByFunBool (fuel : nat) {Δ1 τ1} {Δ2 τ2} (f1 : 𝑭 Δ1 τ1) (f2 : 𝑭 Δ2 τ2) : bool :=
    InvokedByStmWithFuelBool fuel f1 (FunDef f2).

  Lemma InvokedByFun_S_fuel : forall (fuel : nat) {Δ1 τ1} {Δ2 τ2} (f1 : 𝑭 Δ1 τ1) (f2 : 𝑭 Δ2 τ2),
    InvokedByFun fuel f1 f2 ->
    InvokedByFun (S fuel) f1 f2.
  Proof.
    intros fuel Δ1 τ1 Δ2 τ2 f1 f2.
    unfold InvokedByFun.
    apply InvokedByStmWithFuel_S_fuel.
  Qed.

  Definition InvokedByFunPackage (fuel : nat) (f1 f2 : {Δ & {τ & 𝑭 Δ τ}}) : Prop :=
    match f1, f2 with
    | existT Δ1 (existT τ1 f1) ,  existT Δ2 (existT τ2 f2) => InvokedByFun fuel f1 f2
    end.

  Definition InvokedByFunPackageBool (fuel : nat) (f1 f2 : {Δ & {τ & 𝑭 Δ τ}}) : bool :=
    match f1, f2 with
    | existT Δ1 (existT τ1 f1) ,  existT Δ2 (existT τ2 f2) => InvokedByFunBool fuel f1 f2
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

  Section InvokedByReflect.
    Lemma InvokedByStmWithFuel_spec : forall {Δ τ1 τ2 Γ} (fuel : nat) (f : 𝑭 Δ τ1) (s : Stm Γ τ2),
      Bool.reflect (InvokedByStmWithFuel fuel f s) (InvokedByStmWithFuelBool fuel f s).
    Proof.
      intros Δ τ1 τ2 Γ fuel f s.
      apply Bool.iff_reflect. split; intros H.
      - generalize dependent s.
        generalize dependent f.
        generalize dependent Γ.
        generalize dependent τ2.
        generalize dependent τ1.
        generalize dependent Δ.
        induction fuel; intros Δ τ1 τ2 Γ f s H.
        + induction s; cbn in *; auto.
          * apply Bool.orb_true_iff; destruct H as [H|H]; auto.
          * destruct H as [H|?]; auto.
            apply Bool.orb_true_iff. left.
            unfold 𝑭_eq in H. unfold 𝑭_eqb.
            destruct (Classes.eq_dec _ _) eqn:E; auto.
          * apply Bool.orb_true_iff; destruct H as [H|H]; auto.
          * apply Bool.orb_true_iff; destruct H as [H|[pc H]]; auto.
            right. clear IHs.
            apply List.existsb_exists. exists pc. split; auto.
            apply base.elem_of_list_In.
            apply finite.elem_of_enum.
        + induction s; cbn in *; auto.
          * apply Bool.orb_true_iff; destruct H as [H|H]; auto.
          * apply Bool.orb_true_iff; destruct H as [H|H]; auto.
            left. unfold 𝑭_eq in H. unfold 𝑭_eqb.
            destruct (Classes.eq_dec _ _) eqn:E; auto.
          * apply Bool.orb_true_iff; destruct H as [H|H]; auto.
          * apply Bool.orb_true_iff; destruct H as [H|[pc H]]; auto.
            right. clear IHs.
            apply List.existsb_exists. exists pc. split; auto.
            apply base.elem_of_list_In.
            apply finite.elem_of_enum.
      - generalize dependent s.
        generalize dependent f.
        generalize dependent Γ.
        generalize dependent τ2.
        generalize dependent τ1.
        generalize dependent Δ.
        induction fuel; intros Δ τ1 τ2 Γ f s H.
        + induction s; cbn in *; auto.
          * apply Bool.orb_true_iff in H; destruct H; auto.
          * apply Bool.orb_true_iff in H; destruct H; auto.
            left. unfold 𝑭_eqb in H. unfold 𝑭_eq.
            destruct (Classes.eq_dec _ _) eqn:E; auto; try discriminate.
          * apply Bool.orb_true_iff in H; destruct H; auto.
          * apply Bool.orb_true_iff in H; destruct H as [?|[pc [HIn H]]%List.existsb_exists]; auto.
            clear IHs. right. exists pc. auto.
        + induction s; cbn in *; auto.
          * apply Bool.orb_true_iff in H; destruct H; auto.
          * apply Bool.orb_true_iff in H; destruct H; auto.
            left. unfold 𝑭_eqb in H. unfold 𝑭_eq.
            destruct (Classes.eq_dec _ _) eqn:E; auto; try discriminate.
          * apply Bool.orb_true_iff in H; destruct H; auto.
          * apply Bool.orb_true_iff in H; destruct H as [?|[pc [HIn H]]%List.existsb_exists]; auto.
            clear IHs. right. exists pc. auto.
    Qed.

    Lemma InvokedByFunPackage_spec : forall (fuel : nat) (f1 f2 : {Δ & {τ & 𝑭 Δ τ}}),
      Bool.reflect (InvokedByFunPackage fuel f1 f2) (InvokedByFunPackageBool fuel f1 f2).
    Proof.
      unfold InvokedByFunPackage, InvokedByFun.
      intros fuel [Δ1 [τ1 f1]] [Δ2 [τ2 f2]].
      apply InvokedByStmWithFuel_spec.
    Qed.
  End InvokedByReflect.
End ProgramMixin.

Module Type WellFoundedKit (B : Base) (FDecl : FunDecl B) (FDK : FunDefKit B FDecl)
  (Import PM : ProgramMixin B FDecl FDK).

  Parameter Inline 𝑭_well_founded : exists (fuel : nat), well_founded (InvokedByFunPackage fuel).
End WellFoundedKit.

Module Type Program (B : Base) :=
  FunDeclKit B <+ FunDeclMixin B <+ FunDefKit B <+ ProgramMixin B <+ WellFoundedKit B.
