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

Module ContractNotations.
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

  Fixpoint DCtx_to_Args (ctx : DCtx) : LCtx :=
    match ctx with
    | ε => ε
    | Γ ▻ (B x σ) => DCtx_to_Args Γ ▻ (x∷σ)
    | Γ ▻ (destruct_cap _ _ _ _) =>
        let Γ' := DCtx_to_Args Γ in
        let c  := ctx.fresh Γ' (Some "c") in
        Γ' ▻ (c∷ty.cap)
    end.

  #[program] Definition DCtx_to_SStore (Δ : DCtx) (Σ : LCtx) : SStore (DCtx_to_Args Δ) (DCtx_logvars Δ Σ).
  Proof.
    induction Δ.
    - simpl; exact [env].
    - destruct b as [x τ | p b e a].
      + unshelve eapply (env.snoc _ (_∷_) (term_var x)).
        fold DCtx_to_Args.
        apply env.tabulate.
        intros b bIn.
        pose proof (env.lookup IHΔ bIn) as t.
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
        intros b0 b0In.
        pose proof (env.lookup IHΔ b0In) as t.
        unshelve eapply (sub_term t _).
        unfold DCtx_logvars.
        apply sub_up.
        simpl.
        change (DCtx_progvars Δ ▻ p∷ty.perm ▻ b∷ty.addr ▻ e∷ty.addr ▻ a∷ty.addr) with (DCtx_progvars Δ ▻▻ [p∷ty.perm; b∷ty.addr; e∷ty.addr; a∷ty.addr]).
        apply sub_cat_left.
  Defined.

  Module ContractNotations.
    Record Fn {Δ τ} : Set :=
      fn { fnsig : Fun Δ τ;
           args  : DCtx;
           ret   : Ty }.
    Arguments fn {Δ τ} fnsig args%dctx ret.

    Notation "'{{' P '}}' fn '{{' res ',' Q '}}' 'with' logvars" :=
      (MkSepContract (DCtx_to_Args (args fn)) (ret fn) (DCtx_logvars (args fn) logvars%ctx)
         (DCtx_to_SStore (args fn) logvars%ctx)
         P
         res 
         Q) (at level 200, P at level 100, Q at level 100, res at level 100, fn at level 100, logvars at level 100).
    Notation "'{{' P '}}' fn '{{' res ',' Q '}}'" :=
      (MkSepContract (DCtx_to_Args (args fn)) (ret fn) (DCtx_logvars (args fn) []%ctx)
         (DCtx_to_SStore (args fn) []%ctx)
         P
         res 
         Q) (at level 200, P at level 100, Q at level 100, res at level 100, fn at level 100).
  End ContractNotations.

  Module LemmaNotations.
    Record Lm {Δ} : Set :=
      lem { lemsig  : Lem Δ;
            lemargs : DCtx }.
    Arguments lem {Δ} lemsig lemargs%dctx.

    Notation "'{{' P '}}' l '{{' Q '}}' 'with' logvars" :=
      (MkLemma (DCtx_to_Args (lemargs l)) (DCtx_logvars (lemargs l) logvars%ctx)
         (DCtx_to_SStore (lemargs l) logvars%ctx)
         P
         Q) (at level 200, P at level 100, Q at level 100, l at level 100, logvars at level 100).
    Notation "'{{' P '}}' l '{{' Q '}}'" :=
      (MkLemma (DCtx_to_Args (lemargs l)) (DCtx_logvars (lemargs l) []%ctx)
         (DCtx_to_SStore (lemargs l) []%ctx)
         P
         Q) (at level 200, P at level 100, Q at level 100, l at level 100).
  End LemmaNotations.

End ContractNotations.
