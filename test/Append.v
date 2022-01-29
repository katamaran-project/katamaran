(******************************************************************************)
(* Copyright (c) 2021 Steven Keuchel                                          *)
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

From Coq Require Import
     Lists.List
     Logic.FinFun
     Program.Tactics
     Strings.String
     ZArith.ZArith
     micromega.Lia.

From Equations Require Import
     Equations.

From Katamaran Require Import
     Notations
     Semantics.Registers
     Symbolic.Mutator
     Symbolic.Solver
     Symbolic.Worlds
     Symbolic.Propositions
     Program
     Specification
     Sep.Hoare
     Sep.Logic
     Semantics
     Iris.Model.

From stdpp Require decidable finite list fin_maps.
From iris.proofmode Require Import string_ident tactics.

Set Implicit Arguments.
Import ctx.notations.
Import ctx.resolution.
Import env.notations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope ctx_scope.

(*** TERMS ***)

Import DefaultBase.

Module Import ExampleProgram <: Program DefaultBase.

  Notation ptr   := ty_int.
  Notation llist := (ty_option ptr).

  Section FunDeclKit.
    Inductive Fun : PCtx -> Ty -> Set :=
    | append   : Fun [ "p" ∷ ptr, "q" ∷ llist ] ty_unit
    .

    Inductive FunX : PCtx -> Ty -> Set :=
    | mkcons : FunX [ "x" ∷ ty_int, "xs" ∷ llist ] ptr
    (* | head    : FunX [ "p" ∷ ptr ] ty_int *)
    | snd    : FunX [ "p" ∷ ptr ] llist
    (* | sethead : FunX [ "p" ∷ ptr, "x" ∷ ty_int ] ty_unit *)
    | setsnd : FunX [ "p" ∷ ptr, "xs" ∷ llist ] ty_unit
    .

    Definition 𝑭  : PCtx -> Ty -> Set := Fun.
    Definition 𝑭𝑿 : PCtx -> Ty -> Set := FunX.

    Inductive Lem : NCtx 𝑿 Ty -> Set :=
    | open_cons     : Lem [ "p" ∷ ptr ]
    | close_nil     : Lem [ "p" ∷ ty_unit ]
    | close_cons    : Lem [ "p" ∷ ptr ].

    Definition 𝑳 : NCtx 𝑿 Ty -> Set := Lem.

  End FunDeclKit.

  Include FunDeclMixin DefaultBase.

  Section FunDefKit.

    Local Coercion stm_exp : Exp >-> Stm.

    Local Notation "'x'"   := (@exp_var _ "x" _ _) : exp_scope.
    Local Notation "'y'"   := (@exp_var _ "y" _ _) : exp_scope.
    Local Notation "'z'"   := (@exp_var _ "z" _ _) : exp_scope.

    Notation "'lemma' f args" := (stm_lemma f args%arg) (at level 10, f at next level) : exp_scope.

    Definition fun_append : Stm [ "p" ∷ ptr, "q" ∷ llist ] ty_unit :=
      lemma open_cons [exp_var "p"] ;;
      let: "mbn" := foreign snd (exp_var "p") in
      match: (exp_var "mbn") with
      | inl "x" => call append (exp_var "x") (exp_var "q")
      | inr "tt" =>
          lemma close_nil [exp_var "tt"] ;;
          foreign setsnd (exp_var "p") (exp_var "q")
      end;;
      lemma close_cons [exp_var "p"].

    Definition FunDef {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
      Eval compute in
      match f in Fun Δ τ return Stm Δ τ with
      | append => fun_append
      end.

  End FunDefKit.

  Include DefaultRegStoreKit DefaultBase.

  Section ForeignKit.

    Definition Memory : Set := list (Z * (Z + unit)).

    Definition fun_mkcons (elem : Z) (next : Z + unit) (μ : Memory) : Z * Memory :=
      (Zlength μ, app μ (cons (elem,next) nil)).
    (* Definition fun_snd (p : Z) (μ : Memory) : option (option Z) := *)
    (*   let n   := Z.to_nat p in *)
    (*   (* let pre := firstn n μ in *) *)
    (*   let suf := skipn n μ in *)
    (*   match suf with *)
    (*   | nil             => None *)
    (*   | cons (_,next) _ => Some next *)
    (*   end. *)
    (* Definition fun_setsnd (p : Z) (next : option Z) (μ : Memory) : option Memory := *)
    (*   let n   := Z.to_nat p in *)
    (*   let pre := firstn n μ in *)
    (*   let suf := skipn n μ in *)
    (*   match suf with *)
    (*   | nil                => None *)
    (*   | cons (elem,_) suf' => Some (app pre (cons (elem,next) suf')) *)
    (*   end. *)

    Definition ForeignCall {σs σ} (f : 𝑭𝑿 σs σ) :
      forall (args : NamedEnv Val σs) (res : string + Val σ) (γ γ' : RegStore) (μ μ' : Memory), Prop :=
      match f with
      | mkcons => fun args res γ γ' μ μ' =>
                    γ' = γ /\
                    μ' = (μ ++ (args ‼ "x", args ‼ "xs")%exp :: nil) /\
                    res = inr (Zlength μ)
      | snd    => fun args res γ γ' μ μ' =>
                    let n := Z.to_nat (args ‼ "p")%exp in
                    let suf := skipn n μ in
                    match suf with
                    | nil             => res = inl "Invalid pointer"
                    | cons (_,next) _ => γ' = γ /\
                                         μ' = μ /\
                                         res = inr next
                    end
      | setsnd => fun args res γ γ' μ μ' =>
                    let n := Z.to_nat (args ‼ "p")%exp in
                    let pre := firstn n μ in
                    let suf := skipn n μ in
                    match suf with
                    | nil                => res = inl "Invalid pointer"
                    | cons (elem,_) suf' => γ' = γ /\
                                            μ' = (pre ++ (elem, args ‼ "xs")%exp :: suf') /\
                                            res = inr tt
                    end
      end.

    Lemma ForeignProgress {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Val σs) γ μ :
      exists γ' μ' res, ForeignCall f args res γ γ' μ μ'.
    Proof with
          repeat
          match goal with
          | |- _ = _ => reflexivity
          | |- _ /\ _ => split
          | |- exists _, _ => eexists
          end; auto.
      destruct f; unfold ForeignCall.
      - idtac...
      - match goal with
        | |- context[match ?disc with _ => _ end] =>
            destruct disc eqn:?
        end.
        + idtac...
        + destruct p...
      - match goal with
        | |- context[match ?disc with _ => _ end] =>
            destruct disc eqn:?
        end.
        + idtac...
        + destruct p...
    Qed.

  End ForeignKit.

  Include ProgramMixin DefaultBase.

End ExampleProgram.

Inductive Predicate : Set :=
| ptstocons
| ptstolist
.

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for Predicate.

End TransparentObligations.

Derive EqDec for Predicate.

Module Import ExampleSpecification <: Specification DefaultBase.
  Module PROG := ExampleProgram.
  Import DefaultBase.

  Include DefaultPurePredicateKit DefaultBase.

  Section HeapPredicateDeclKit.

    Definition 𝑯 := Predicate.
    Definition 𝑯_Ty (p : 𝑯) : Ctx Ty :=
      match p with
      | ptstocons => [ptr, ty_int, llist]
      | ptstolist => [llist, ty_list ty_int]
      end.
    Instance 𝑯_eq_dec : EqDec 𝑯 := Predicate_eqdec.
    Global Instance 𝑯_is_dup : IsDuplicable 𝑯 :=
      {| is_duplicable p := false |}.

    Local Arguments Some {_} &.
    Definition 𝑯_precise (p : 𝑯) : option (Precise 𝑯_Ty p) :=
      match p with
      | ptstocons => Some (MkPrecise [ptr] [ptr, llist] eq_refl)
      | ptstolist => Some (MkPrecise [llist] [ty_list ptr] eq_refl)
      end.

  End HeapPredicateDeclKit.

  Include ContractDeclMixin DefaultBase ExampleProgram.

  Section ContractDefKit.

    Import ctx.resolution.

    Local Notation "p '↦l' xs" := (asn_chunk (chunk_user ptstolist (env.nil ► (llist ↦ p) ► (ty_list ty_int ↦ xs)))) (at level 70).
    Local Notation "p '∗' q" := (asn_sep p q).
    Local Notation "p '↦p' ( x , xs )" := (asn_chunk (chunk_user ptstocons (env.nil ► (ptr ↦ p) ► (ty_int ↦ x) ► (llist ↦ xs)))) (at level 70).

    Arguments formula_prop [Σ] Σ' ζ _.

    Definition asn_append {Σ : LCtx} (xs ys zs : Term Σ (ty_list ty_int)) : Assertion Σ :=
      asn_formula (formula_eq (term_binop binop_append xs ys) zs).

    Definition sep_contract_append : SepContract [ "p" ∷ ptr, "q" ∷ llist ] ty_unit :=
      {| sep_contract_logic_variables := ["p" ∷ ptr, "q" ∷ llist, "xs" ∷ ty_list ty_int, "ys" ∷ ty_list ty_int];
         sep_contract_localstore      := [term_var "p", term_var "q"]%arg;
         sep_contract_precondition    := term_inl (term_var "p") ↦l term_var "xs" ∗ term_var "q" ↦l term_var "ys";
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
           asn_formula (formula_eq (term_var "result") (term_val ty_unit tt)) ∗
           asn_exist "zs" (ty_list ty_int)
             (term_inl (term_var "p") ↦l term_var "zs" ∗
              asn_append (term_var "xs") (term_var "ys") (term_var "zs"));
      |}.

    Definition sep_contract_mkcons : SepContract [ "x" ∷ ty_int, "xs" ∷ llist ] ptr :=
      {| sep_contract_logic_variables := ["x" ∷ ty_int, "xs" ∷ llist];
         sep_contract_localstore      := [term_var "x", term_var "xs"]%arg;
         sep_contract_precondition    := asn_true;
         sep_contract_result          := "p";
         sep_contract_postcondition   := term_var "p" ↦p ( term_var "x" , term_var "xs" );
      |}.

    Definition sep_contract_snd : SepContract [ "p" ∷ ptr ] llist :=
      {| sep_contract_logic_variables := ["p" ∷ ty_int, "x" ∷ ty_int, "xs" ∷ llist];
         sep_contract_localstore      := [term_var "p"]%arg;
         sep_contract_precondition    := term_var "p" ↦p ( term_var "x" , term_var "xs" );
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
           asn_formula (formula_eq (term_var "result") (term_var "xs")) ∗
           term_var "p" ↦p ( term_var "x" , term_var "xs" );
      |}.

    Definition sep_contract_setsnd : SepContract [ "p" ∷ ptr, "xs" ∷ llist ] ty_unit :=
      {| sep_contract_logic_variables := ["p" ∷ ty_int, "x" ∷ ty_int, "xs" ∷ llist];
         sep_contract_localstore      := [term_var "p", term_var "xs"]%arg;
         sep_contract_precondition    := asn_exist "ys" llist (term_var "p" ↦p ( term_var "x" , term_var "ys"));
         sep_contract_result          := "result";
         sep_contract_postcondition   :=
         asn_formula (formula_eq (term_var "result") (term_val ty_unit tt)) ∗
         term_var "p" ↦p ( term_var "x" , term_var "xs");
      |}.

    Definition sep_lemma_open_cons : Lemma [ "p" ∷ ptr ] :=
      {| lemma_logic_variables := ["p" ∷ ty_int, "xs" ∷ ty_list ty_int];
         lemma_patterns        := [term_var "p"]%arg;
         lemma_precondition    := term_inl (term_var "p") ↦l term_var "xs";
         lemma_postcondition   :=
           asn_match_list (term_var "xs")
             asn_false
             "y" "ys"
             (asn_exist "n" llist
                (term_var "p" ↦p (term_var "y", term_var "n") ∗
                term_var "n" ↦l term_var "ys"))
      |}.

    Definition sep_lemma_close_cons : Lemma [ "p" ∷ ptr ] :=
      {| lemma_logic_variables := ["p" ∷ ptr, "x" ∷ ty_int, "xs" ∷ ty_list ty_int, "n" ∷ llist ];
         lemma_patterns        := [term_var "p"]%arg;
         lemma_precondition    := term_var "p" ↦p (term_var "x" , term_var "n") ∗
                                  term_var "n" ↦l term_var "xs";
         lemma_postcondition   := term_inl (term_var "p") ↦l term_binop binop_cons (term_var "x") (term_var "xs")
      |}.

    Definition sep_lemma_close_nil : Lemma [ "p" ∷ ty_unit ] :=
      {| lemma_logic_variables := ["p" ∷ ty_unit, "xs" ∷ ty_list ty_int ];
         lemma_patterns        := [term_var "p"]%arg;
         lemma_precondition    := term_inr (term_var "p") ↦l term_var "xs";
         lemma_postcondition   :=
           asn_formula (formula_eq (term_var "p") (term_val ty_unit tt)) ∗
           asn_formula (formula_eq (term_var "xs") (term_val (ty_list ty_int) nil))
      |}.

    Definition CEnv : SepContractEnv :=
      fun Δ τ f =>
        match f with
        | append => Some (sep_contract_append)
        end.

    Definition CEnvEx : SepContractEnvEx :=
      fun Δ τ f =>
        match f with
        | mkcons => sep_contract_mkcons
        | snd => sep_contract_snd
        | setsnd => sep_contract_setsnd
        end.

    Definition LEnv : LemmaEnv :=
      fun Δ l =>
        match l with
        | open_cons => sep_lemma_open_cons
        | close_cons => sep_lemma_close_cons
        | close_nil => sep_lemma_close_nil
        end.

  End ContractDefKit.

  Include SpecificationMixin DefaultBase ExampleProgram.

End ExampleSpecification.

Module ExampleSolverKit := DefaultSolverKit DefaultBase ExampleSpecification.
Module ExampleSolver := MakeSolver DefaultBase ExampleSpecification ExampleSolverKit.

Module Import ExampleExecutor :=
  MakeExecutor DefaultBase ExampleSpecification ExampleSolver.

Lemma valid_contract_append : SMut.ValidContractReflect sep_contract_append fun_append.
Proof. Time reflexivity. Qed.

Module ExampleSemantics <: Semantics DefaultBase ExampleProgram :=
  MakeSemantics DefaultBase ExampleProgram.

Module ExampleModel.
  Import ExampleProgram.
  Import ExampleSpecification.

  Include ProgramLogicOn DefaultBase ExampleSpecification.
  Include Iris DefaultBase ExampleSpecification ExampleSemantics.

  Module ExampleIrisHeapKit <: IrisHeapKit.
    Section WithIrisNotations.
      Import iris.bi.interface.
      Import iris.bi.big_op.
      Import iris.base_logic.lib.iprop.
      Import iris.base_logic.lib.gen_heap.

      Class mcMemGS Σ :=
        McMemGS {
            (* ghost variable for tracking state of registers *)
            mc_ghGS :> gen_heapGS nat (Z * (Z + unit)) Σ;
            mc_invNs : namespace
          }.
 
      Definition memGpreS : gFunctors -> Set := fun Σ => gen_heapGpreS nat (Z * (Z + unit)) Σ.
      Definition memGS : gFunctors -> Set := mcMemGS.
      Definition memΣ : gFunctors := gen_heapΣ nat (Z * (Z + unit)).

      Definition memΣ_GpreS : forall {Σ}, subG memΣ Σ -> memGpreS Σ :=
        fun {Σ} => subG_gen_heapGpreS (Σ := Σ) (L := nat) (V := (Z * (Z + unit))).

      Definition memToGmap (μ : Memory) : gmap nat (Z * (Z + unit)) :=
        list_to_map (imap pair μ).

      Lemma memToGmap_lookup_length (μ : Memory) :
        memToGmap μ !! length μ = None.
      Admitted.

      Lemma memToGmap_app (μ : Memory) (v : Z * (Z + unit)) :
        memToGmap (μ ++ cons v nil) = <[length μ:=v]> (memToGmap μ).
      Proof.
        unfold memToGmap.
        rewrite imap_app.
        rewrite list_to_map_app; cbn.
        rewrite <- list_to_map_nil.
        rewrite <- list_to_map_cons.
        rewrite <- list_to_map_app.
        rewrite Nat.add_0_r.
        rewrite list_to_map_snoc; first reflexivity.
        rewrite not_elem_of_list_to_map.
        apply memToGmap_lookup_length.
      Qed.

      Definition mem_inv : forall {Σ}, memGS Σ -> Memory -> iProp Σ :=
        fun {Σ} hG μ => (gen_heap_interp (hG := mc_ghGS (mcMemGS := hG)) (memToGmap μ))%I.

      Definition mem_res : forall {Σ}, memGS Σ -> Memory -> iProp Σ :=
        fun {Σ} hG μ => ([∗ map] l↦v ∈ memToGmap μ, mapsto (hG := mc_ghGS (mcMemGS := hG)) l (DfracOwn 1) v)%I.

      Lemma mem_inv_init : forall Σ (μ : Memory), memGpreS Σ ->
        ⊢ |==> ∃ mG : memGS Σ, (mem_inv mG μ ∗ mem_res mG μ)%I.
      Proof.
        iIntros (Σ μ gHP).
        iMod (gen_heap_init (gen_heapGpreS0 := gHP) (L := nat) (V := (Z * (Z + unit))) empty) as (gH) "[inv _]".

        pose (memmap := memToGmap μ).
        iMod (gen_heap_alloc_big empty memmap (map_disjoint_empty_r memmap) with "inv") as "(inv & res & _)".
        iModIntro.
        rewrite (right_id empty union memmap).

        iExists (McMemGS gH (nroot .@ "mem_inv")).
        iFrame.
      Qed.

      Definition ptstocons_interp `{mG : memGS Σ} (p : Z) (v : Z) (n : Z + unit) : iProp Σ :=
        (∃ p', ⌜p = Z.of_nat p'⌝ ∗
              mapsto (hG := mc_ghGS (mcMemGS := mG)) p' (DfracOwn 1) (pair v n))%I.

      Fixpoint ptstolist_interp `{mG : memGS Σ} (p : Z + unit) (vs : list Z) : iProp Σ :=
        match vs with
        | nil => ⌜p = inr tt⌝
        | v :: vs => (∃ p' pn, ⌜p = inl p'⌝ ∗ ptstocons_interp (mG := mG) p' v pn ∗ ptstolist_interp (mG := mG) pn vs)%I
      end.

    Definition luser_inst `{sailRegGS Σ} `{wsat.invGS.invGS Σ} (mG : memGS Σ) (p : Predicate) (ts : Env Val (𝑯_Ty p)) : iProp Σ :=
      (match p return Env Val (𝑯_Ty p) -> iProp Σ with
      | ptstocons => fun ts => ptstocons_interp (mG := mG) (env.head (env.tail (env.tail ts))) (env.head (env.tail ts)) (env.head ts)
      | ptstolist => fun ts => ptstolist_interp (mG := mG) (env.head (env.tail ts)) (env.head ts)
       end) ts.

    Definition lduplicate_inst `{sailRegGS Σ} `{wsat.invGS.invGS Σ} (mG : memGS Σ) :
      forall (p : Predicate) (ts : Env Val (𝑯_Ty p)),
      is_duplicable p = true -> luser_inst mG p ts -∗ luser_inst mG p ts ∗ luser_inst mG p ts.
    Proof.
      destruct p; now cbn.
    Qed.

    Unset Printing Notations.
    Set Printing Implicit.
    End WithIrisNotations.
  End ExampleIrisHeapKit.

  Import ExampleIrisHeapKit.

  Module Import RiscvPmpIrisInstance := IrisInstance ExampleIrisHeapKit.

  Section WithIrisNotations.
    Import iris.bi.interface.
    Import iris.bi.big_op.
    Import iris.base_logic.lib.iprop.
    Import iris.program_logic.weakestpre.
    Import iris.base_logic.lib.gen_heap.

    Ltac destruct_syminstance ι :=
      repeat
        match type of ι with
        | Env _ (ctx.snoc _ (MkB ?s _)) =>
            let id := string_to_ident s in
            let fr := fresh id in
            destruct (env.snocView ι) as [ι fr];
            destruct_syminstance ι
        | Env _ ctx.nil => destruct (env.nilView ι)
        | _ => idtac
        end.

    Lemma mkcons_sound `{sg : sailGS Σ} `{invGS} {Γ es δ} :
      forall (x : Val ptr) (l : Val llist),
        evals es δ = env.snoc (env.snoc env.nil (MkB _ ptr) x) (MkB _ llist) l
        → ⊢ semTriple δ (⌜true = true⌝ ∧ emp) (stm_foreign mkcons es)
            (λ (v : Val ptr) (δ' : CStore Γ),
              ptstocons_interp v x l ∗ ⌜δ' = δ⌝).
    Proof.
      intros x l Heq.
      iIntros "_".
      rewrite wp_unfold. cbn.
      iIntros (σ' ns ks1 ks nt) "[Hregs Hmem]".
      unfold mem_inv.
      iMod (fupd_mask_subseteq empty) as "Hclose2"; first set_solver.
      iModIntro.
      iSplitR; first by intuition.
      iIntros (e2 σ'' efs) "%".
      dependent elimination H0.
      dependent elimination s.
      cbn in f1.
      destruct_conjs; subst.
      do 3 iModIntro.
      rewrite Heq.
      cbn -[memToGmap].
      rewrite memToGmap_app.
      iMod "Hclose2" as "_".
      iMod (gen_heap_alloc (memToGmap μ1) (length μ1) (x,l) with "Hmem") as "[Hmem [Hres _]]".
      { now eapply memToGmap_lookup_length. }
      iModIntro.
      iFrame.
      iSplitL; last done.
      iApply wp_value.
      cbn.
      iSplitL; last done.
      iExists (length μ1); iFrame.
      iPureIntro.
      eapply Zlength_correct.
    Qed.

    Lemma snd_sound `{sg : sailGS Σ} `{invGS} {Γ es δ} :
      forall (xs : Val llist)
        (x p : Val ptr),
        evals es δ = env.snoc env.nil (MkB _ ptr) p ->
        ⊢ semTriple δ
          (ptstocons_interp p x xs)
          (stm_foreign snd es)
          (λ (v : Z + ()) (δ' : CStore Γ),
            ((⌜v = xs⌝ ∧ emp) ∗ ptstocons_interp p x xs) ∗ ⌜ δ' = δ⌝).
    Proof.
    Admitted.

    Lemma setsnd_sound `{sg : sailGS Σ} `{invGS} {Γ es δ} :
      forall (xs : Val llist) (x p : Val ptr),
        evals es δ = env.snoc (env.snoc env.nil (MkB _ ptr) p) (MkB _ llist) xs →
        ⊢ semTriple δ
        (∃ v : Z + (), ptstocons_interp p x v)
        (stm_foreign setsnd es)
        (λ (v : ()) (δ' : CStore Γ),
           ((⌜v = tt⌝ ∧ emp) ∗ ptstocons_interp p x xs) ∗ ⌜
           δ' = δ⌝).
    Proof.
    Admitted.

    Lemma foreignSem `{sg : sailGS Σ} : ForeignSem (Σ := Σ).
    Proof.
      intros Γ τ Δ f es δ.
      destruct f; cbn;
        intros ι; destruct_syminstance ι;
        eauto using mkcons_sound, snd_sound, setsnd_sound.
    Qed.

    Lemma lemSem `{sg : sailGS Σ} : LemmaSem (Σ := Σ).
    Proof.
    Admitted.

  End WithIrisNotations.
End ExampleModel.
