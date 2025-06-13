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

From stdpp Require Import base finite list.
From Katamaran Require Export
     Syntax.FunDecl
     Syntax.FunDef
     Syntax.Statements
     Base.

Module Type FunDeclMixin (B : Base) :=
  StatementsOn B.

Module Type ProgramMixin (Import B : Base)
  (Import FDecl : FunDecl B)
  (Import FDK : FunDefKit B FDecl).

  Module Import callgraph.

    Notation Node := {Δ & {τ & 𝑭 Δ τ}}.
    Notation Nodes := (list Node).
    Definition CallGraph : Set := Node -> Nodes.

    Definition InvokedBy (g : CallGraph) (f1 f2 : Node) : Prop :=
      f1 ∈ g f2.

    Class Accessible (g : CallGraph) (f : Node) : Prop :=
      accessible : Acc (InvokedBy g) f.

    Lemma accessible_intro (g : CallGraph) (f : Node) :
      List.Forall (Accessible g) (g f) -> Accessible g f.
    Proof. rewrite Forall_forall. now constructor. Qed.

    Section WithNodes.
      Context (fs : Nodes).

      Fixpoint StmWellFormed {Δ τ} (s : Stm Δ τ) : Prop :=
        match s with
        | stm_val _ v => True
        | stm_exp e => True
        | stm_let x σ s1 s2 => StmWellFormed s1 /\ StmWellFormed s2
        | stm_block δ s => StmWellFormed s
        | stm_assign xInΓ s => StmWellFormed s
        | stm_call f2 es => (existT _ (existT _ f2)) ∈ fs
        | stm_call_frame δ s => StmWellFormed s
        | stm_foreign f es => True
        | stm_lemmak l es k => StmWellFormed k
        | stm_seq s k => StmWellFormed s /\ StmWellFormed k
        | stm_assertk e1 e2 k => StmWellFormed k
        | stm_fail _ s => True
        | stm_pattern_match s pat rhs =>
            StmWellFormed s /\ (forall pc, StmWellFormed (rhs pc))
        | stm_read_register reg => True
        | stm_write_register reg e => True
        | @stm_bind _ _ σ s k => StmWellFormed s /\
                          (forall (v : Val σ), StmWellFormed (k v))
        | stm_debugk k => StmWellFormed k
        end.

    End WithNodes.

    Fixpoint InvokedByStmList {Γ τ} (s : Stm Γ τ) : Nodes :=
      match s with
      | stm_val _ v => []
      | stm_exp e => []
      | stm_let x σ s1 s2 => InvokedByStmList s1 ++ InvokedByStmList s2
      | stm_block δ s => InvokedByStmList s
      | stm_assign xInΓ s => InvokedByStmList s
      | stm_call f2 es => [existT _ (existT _ f2)]
      | stm_call_frame δ s => InvokedByStmList s
      | stm_foreign f es => []
      | stm_lemmak l es k => InvokedByStmList k
      | stm_seq s k => InvokedByStmList s ++ InvokedByStmList k
      | stm_assertk e1 e2 k => InvokedByStmList k
      | stm_fail _ s => []
      | stm_pattern_match s pat rhs =>
          InvokedByStmList s ++
            List.flat_map
            (fun pc => InvokedByStmList (rhs pc))
            (enum (PatternCase pat))
      | stm_read_register reg => []
      | stm_write_register reg e => []
      | stm_bind s k => InvokedByStmList s
      | stm_debugk k => InvokedByStmList k
      end%list.

    Lemma InvokedByStmList_WellFormed_aux {Γ τ} (s : Stm Γ τ) :
      forall (fs : Nodes),
        InvokedByStmList s ⊆ fs ->
        StmWellFormed fs s.
    Proof.
      induction s; cbn; intros fs sub_fs;
        try
          match type of sub_fs with
          | ?fs1 ++ ?fs2 ⊆ ?fs =>
              apply list_subseteq_app_iff_l in sub_fs;
              destruct sub_fs as [sub_fs1 sub_fs2]
          end;
        repeat
          match goal with
          | |- ?f ∈ cons ?f _ => constructor 1
          | H: ?ls ⊆ ?fs |- ?f ∈ ?fs =>
              match ls with
                context[f] => apply H; clear fs H
              end
          | |- _ ∧ _ => split
          end;
        auto.
      - intros pc. apply H. intros h hIn. apply sub_fs2.
        apply elem_of_list_In, in_flat_map. exists pc.
        split; apply elem_of_list_In; auto.
        apply elem_of_enum.
      - admit.
    Admitted.

    Lemma InvokedByStmList_WellFormed {Γ τ} (s : Stm Γ τ) :
      StmWellFormed (InvokedByStmList s) s.
    Proof. now apply InvokedByStmList_WellFormed_aux. Qed.

    Definition CallGraphWellFormed (g : CallGraph) : Prop :=
      forall Δ τ (f : 𝑭 Δ τ),
        StmWellFormed (g (existT _ (existT _ f))) (FunDef f).

  End callgraph.

  (* TODO: remove duplicates from calculated list *)
  Definition 𝑭_call_graph : CallGraph :=
    fun '(existT _ (existT _ f)) => InvokedByStmList (FunDef f).

  Lemma 𝑭_call_graph_wellformed : CallGraphWellFormed 𝑭_call_graph.
  Proof. intros Δ τ f. apply InvokedByStmList_WellFormed. Qed.

  Notation AccessibleFun f := (Accessible 𝑭_call_graph (existT _ (existT _ f))).

End ProgramMixin.

Module Type WellFoundedKit (B : Base) (Import FDecl : FunDecl B)
  (Import FDK : FunDefKit B FDecl)
  (Import PM : ProgramMixin B FDecl FDK).

  Parameter 𝑭_accessible :
    forall Δ τ (f : 𝑭 Δ τ), option (AccessibleFun f).

End WellFoundedKit.

Module Type Program (B : Base) :=
  FunDeclKit B <+ FunDeclMixin B <+ FunDefKit B <+ ProgramMixin B <+ WellFoundedKit B.
