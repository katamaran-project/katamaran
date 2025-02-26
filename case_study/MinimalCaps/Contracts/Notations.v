(******************************************************************************)
(* Copyright (c) 2023 Steven Keuchel, Dominique Devriese, Sander Huyghebaert  *)
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
  Strings.String.
From Katamaran Require Import
  MinimalCaps.Machine
  MinimalCaps.Sig
  Specification.

Import ctx.notations.
Import ctx.resolution.
Import env.notations.
Import MinCapsSignature.
Open Scope string_scope.
Open Scope ctx_scope.

Module Notations.
  Inductive MinCapsBinding : Set :=
  | B (name : string) (type : Ty)
  | destruct_cap (p b e a : string).

  Definition DCtx := Ctx MinCapsBinding.

  Declare Scope dctx_scope.
  Delimit Scope dctx_scope with dctx.
  Notation "x '::' τ" := (B x τ) : dctx_scope.
  Notation "'(' p ',' b ',' e ',' a ')' '::' 'ty.cap'" :=
    (destruct_cap p b e a) : dctx_scope.
  (* Use the same notations as in ctx.notations *)
  Notation "[ ]" := (ctx.nil) : dctx_scope.
  Notation "[ctx]" := (ctx.nil) : dctx_scope.
  Notation "[ x ]" := (ctx.snoc ctx.nil x%dctx) : dctx_scope.
  Notation "[ x ; y ; .. ; z ]" :=
    (ctx.snoc .. (ctx.snoc (ctx.snoc ctx.nil x%dctx) y%dctx) .. z%dctx) : dctx_scope.

  Fixpoint DCtx_to_PCtx (ctx : DCtx) : PCtx :=
    match ctx with
    | ε => ε
    | Γ ▻ (B x σ) => DCtx_to_PCtx Γ ▻ (x∷σ)
    | Γ ▻ (destruct_cap p b e a) =>
        DCtx_to_PCtx Γ ▻ (p∷ty.perm) ▻ (b∷ty.addr) ▻ (e∷ty.addr) ▻ (a∷ty.addr)
    end.

  Fixpoint DCtx_progvars (ctx : DCtx) : LCtx :=
    match ctx with
    | ε => ε
    | Γ ▻ (B x σ) => DCtx_progvars Γ ▻ (x∷σ)
    | Γ ▻ (destruct_cap p b e a) =>
        DCtx_progvars Γ ▻ (p∷ty.perm) ▻ (b∷ty.addr) ▻ (e∷ty.addr) ▻ (a∷ty.addr)
    end.

  Definition DCtx_logvars (Δ : DCtx) (Σ : LCtx) :=
    DCtx_progvars Δ ▻▻ Σ.

  Fixpoint DCtx_to_Args (ctx : DCtx) (names : LCtx) : LCtx :=
    match ctx, names with
    | ε , _ => ε
    | _ , ε => ε
    | Γ ▻ (B x σ) , Δ ▻ _ => DCtx_to_Args Γ Δ ▻ (x∷σ)
    | Γ ▻ (destruct_cap _ _ _ _) , Δ ▻ (c∷_) =>
        let Γ' := DCtx_to_Args Γ Δ in
        Γ' ▻ (c∷ty.cap)
    end.

  #[program] Definition DCtx_to_SStore (Δ : DCtx) (names : LCtx) (Σ : LCtx) : SStore (DCtx_to_Args Δ names) (DCtx_logvars Δ Σ).
  Proof.
    generalize dependent names.
    induction Δ.
    - destruct names; simpl; exact [env].
    - destruct names; simpl; first (destruct b; exact [env]).
      destruct b as [x τ | p b e a].
      + unshelve eapply (env.snoc _ (_∷_) (term_var x)).
        fold DCtx_to_Args.
        apply env.tabulate.
        intros b bIn.
        pose proof (env.lookup (IHΔ names) bIn) as t.
        unshelve eapply (sub_term t _).
        unfold DCtx_logvars.
        simpl.
        apply sub_up.
        apply sub_wk1.
        simpl.
        unfold DCtx_logvars.
        apply ctx.in_cat_left.
        simpl.
        apply ctx.in_zero.
      + unfold DCtx_logvars; simpl.
        unshelve eapply
          (env.snoc _ (_∷_)
             (term_record capability [env].["cap_permission"∷ty.perm ↦ term_var p]
              .["cap_begin"∷ty.addr       ↦ term_var b]
              .["cap_end"∷ty.addr         ↦ term_var e]
              .["cap_cursor"∷ty.addr      ↦ term_var a])); simpl;
          repeat
            (try apply ctx.in_cat_left;
             try apply ctx.in_zero;
             apply ctx.in_succ).
        apply env.tabulate.
        intros b1 b1In.
        pose proof (env.lookup (IHΔ names) b1In) as t.
        unshelve eapply (sub_term t _).
        unfold DCtx_logvars.
        apply sub_up.
        simpl.
        change (DCtx_progvars Δ ▻ p∷ty.perm ▻ b∷ty.addr ▻ e∷ty.addr ▻ a∷ty.addr) with (DCtx_progvars Δ ▻▻ [p∷ty.perm; b∷ty.addr; e∷ty.addr; a∷ty.addr]).
        apply sub_cat_left.
  Defined.

  (* TODO: following module needs to move into this file *)
  Import MinCapsContractNotations.

  (* 𝒱 should only be used with terms of type word or cap, otherwise it just
     returns bottom *)
  Definition 𝒱 {Σ τ} : Term Σ τ -> Assertion Σ :=
    match τ with
    | ty.word => fun w => asn_safe w
    | ty.cap  => fun w => asn_csafe w
    | ty.int  => fun w => asn_safe (term_inl w)
    | _       => fun _ => ⊥
    end.

  Declare Scope term_scope.
  Delimit Scope term_scope with term.
  Notation "'(' tp ',' tb ',' te ',' ta ')'" :=
    (term_record capability [tp; tb; te; ta]) : term_scope.
  Notation "t1 '+' t2" :=
    (term_binop bop.plus t1 t2) : term_scope.
  Notation "'𝒱' '(' tp ',' tb ',' te ',' ta ')'" :=
    (𝒱 (term_record capability [tp; tb; te; ta])) : term_scope.
  Notation "'𝒱' '(' t ')'" :=
    (𝒱 t) : term_scope.

  Module ContractNotations.
    Record Fn {Δ τ} : Set :=
      fn { fnsig : Fun Δ τ;
           args  : DCtx;
           ret   : Ty }.
    Arguments fn {Δ τ} fnsig args%_dctx ret.

    Definition fnsig_args {Δ τ} (f : @Fn Δ τ) := Δ.

    Notation "'{{' P '}}' fn '{{' res ',' Q '}}' 'with' logvars" :=
      (MkSepContract (DCtx_to_Args (args fn) (fnsig_args fn)) (ret fn) (DCtx_logvars (args fn) logvars%ctx)
         (DCtx_to_SStore (args fn) (fnsig_args fn) logvars%ctx)
         P%term
         res
         Q%term) (at level 200, P at level 100, Q at level 100, res at level 100, fn at level 100, logvars at level 100).
    Notation "'{{' P '}}' fn '{{' res ',' Q '}}'" :=
      (MkSepContract (DCtx_to_Args (args fn) (fnsig_args fn)) (ret fn) (DCtx_logvars (args fn) []%ctx)
         (DCtx_to_SStore (args fn) (fnsig_args fn) []%ctx)
         P%term
         res
         Q%term) (at level 200, P at level 100, Q at level 100, res at level 100, fn at level 100).
  End ContractNotations.

  Module LemmaNotations.
    Record Lm {Δ} : Set :=
      lem { lemsig  : Lem Δ;
            lemargs : DCtx }.
    Arguments lem {Δ} lemsig lemargs%_dctx.

    Definition lemsig_args {Δ} (l : @Lm Δ) := Δ.

    Notation "'{{' P '}}' l '{{' Q '}}' 'with' logvars" :=
      (MkLemma (DCtx_to_Args (lemargs l) (lemsig_args l)) (DCtx_logvars (lemargs l) logvars%ctx)
         (DCtx_to_SStore (lemargs l) (lemsig_args l) logvars%ctx)
         P%term
         Q%term) (at level 200, P at level 100, Q at level 100, l at level 100, logvars at level 100).
    Notation "'{{' P '}}' l '{{' Q '}}'" :=
      (MkLemma (DCtx_to_Args (lemargs l) (lemsig_args l)) (DCtx_logvars (lemargs l) []%ctx)
         (DCtx_to_SStore (lemargs l) (lemsig_args l) []%ctx)
         P%term
         Q%term) (at level 200, P at level 100, Q at level 100, l at level 100).
  End LemmaNotations.

  Module ForeignNotations.
    Record FnX {Δ τ} : Set :=
      fn { fnsig : FunX Δ τ; (* Funx <> Fun (see Fn record) *)
           args  : DCtx;
           ret   : Ty }.
    Arguments fn {Δ τ} fnsig args%_dctx ret.

    Definition fnsig_args {Δ τ} (f : @FnX Δ τ) := Δ.

    Notation "'{{' P '}}' fn '{{' res ',' Q '}}' 'with' logvars" :=
      (MkSepContract (DCtx_to_Args (args fn) (fnsig_args fn)) (ret fn) (DCtx_logvars (args fn) logvars%ctx)
         (DCtx_to_SStore (args fn) (fnsig_args fn) logvars%ctx)
         P%term
         res
         Q%term) (at level 200, P at level 100, Q at level 100, res at level 100, fn at level 100, logvars at level 100).
    Notation "'{{' P '}}' fn '{{' res ',' Q '}}'" :=
      (MkSepContract (DCtx_to_Args (args fn) (fnsig_args fn)) (ret fn) (DCtx_logvars (args fn) []%ctx)
         (DCtx_to_SStore (args fn) (fnsig_args fn) []%ctx)
         P%term
         res
         Q%term) (at level 200, P at level 100, Q at level 100, res at level 100, fn at level 100).
  End ForeignNotations.
End Notations.
