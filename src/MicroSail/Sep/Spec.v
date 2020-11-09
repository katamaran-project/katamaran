(******************************************************************************)
(* Copyright (c) 2019 Steven Keuchel                                          *)
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

From Coq Require
     Vector.

From MicroSail Require Import
     Notation
     Sep.Logic
     Syntax.

From Equations Require Import
     Equations.

Import CtxNotations.
Import EnvNotations.

Set Implicit Arguments.

Module Type AssertionKit
       (termkit : TermKit)
       (Export progkit : ProgramKit termkit).

  (* Predicate names. *)
  Parameter Inline 𝑷  : Set.
  (* Predicate field types. *)
  Parameter Inline 𝑷_Ty : 𝑷 -> Ctx Ty.
  Declare Instance 𝑷_eq_dec : EqDec 𝑷.

End AssertionKit.

Module Assertions
       (termkit : TermKit)
       (progkit : ProgramKit termkit)
       (Export assertkit : AssertionKit termkit progkit).

  Inductive Chunk (Σ : Ctx (𝑺 * Ty)) : Type :=
  | chunk_pred   (p : 𝑷) (ts : Env (Term Σ) (𝑷_Ty p))
  | chunk_ptsreg {σ : Ty} (r : 𝑹𝑬𝑮 σ) (t : Term Σ σ).
  Arguments chunk_pred [_] _ _.

  Inductive Assertion (Σ : Ctx (𝑺 * Ty)) : Type :=
  | asn_bool (b : Term Σ ty_bool)
  | asn_prop (P : abstract_named Lit Σ Prop)
  | asn_eq {T : Ty} (t1 t2 : Term Σ T)
  | asn_chunk (c : Chunk Σ)
  | asn_if   (b : Term Σ ty_bool) (a1 a2 : Assertion Σ)
  | asn_match_enum {E : 𝑬} (k : Term Σ (ty_enum E)) (alts : forall (K : 𝑬𝑲 E), Assertion Σ)
  | asn_sep  (a1 a2 : Assertion Σ)
  | asn_exist (ς : 𝑺) (τ : Ty) (a : Assertion (Σ ▻ (ς , τ))).

  Definition asn_true {Σ} : Assertion Σ :=
    asn_bool (term_lit ty_bool true).
  Definition asn_false {Σ} : Assertion Σ :=
    asn_bool (term_lit ty_bool false).

  Arguments asn_prop {_} _.
  Arguments asn_match_enum [_] _ _ _.
  Arguments asn_exist [_] _ _ _.

  Instance sub_chunk : Subst Chunk :=
    fun Σ1 Σ2 ζ c =>
      match c with
      | chunk_pred p ts => chunk_pred p (subst ζ ts)
      | chunk_ptsreg r t => chunk_ptsreg r (subst ζ t)
      end.

  Instance substlaws_chunk : SubstLaws Chunk.
  Proof.
    constructor.
    { intros ? []; cbn; f_equal; apply subst_sub_id. }
    { intros ? ? ? ? ? []; cbn; f_equal; apply subst_sub_comp. }
  Qed.

  (* Fixpoint sub_assertion {Σ1 Σ2} (ζ : Sub Σ1 Σ2) (a : Assertion Σ1) {struct a} : Assertion Σ2 := *)
  (*   match a with *)
  (*   | asn_bool b => asn_bool (sub_term ζ b) *)
  (*   | asn_chunk c => asn_chunk (sub_chunk ζ c) *)
  (*   | asn_if b a1 a2 => asn_if (sub_term ζ b) (sub_assertion ζ a1) (sub_assertion ζ a2) *)
  (*   | asn_match_enum k alts => *)
  (*     asn_match_enum (sub_term ζ k) (fun z => sub_assertion ζ (alts z)) *)
  (*   | asn_sep a1 a2 => asn_sep (sub_assertion ζ a1) (sub_assertion ζ a2) *)
  (*   | asn_exist ς τ a => asn_exist ς τ (sub_assertion (sub_up1 ζ) a) *)
  (*   end. *)

  (* Definition SymbolicRegStore (Σ : Ctx (𝑺 * Ty))  : Type := forall σ, 𝑹𝑬𝑮 σ -> Term Σ σ. *)


  Definition symbolic_eval_exp {Γ Σ} (δ : SymbolicLocalStore Γ Σ) :
    forall {σ} (e : Exp Γ σ), Term Σ σ :=
    fix symbolic_eval_exp {σ} (e : Exp Γ σ) : Term Σ σ :=
      match e with
      | exp_var ς                => δ ‼ ς
      | exp_lit σ l              => term_lit σ l
      | exp_binop op e1 e2       => term_binop op (symbolic_eval_exp e1) (symbolic_eval_exp e2)
      | exp_neg e                => term_neg (symbolic_eval_exp e)
      | exp_not e                => term_not (symbolic_eval_exp e)
      | exp_inl e                => term_inl (symbolic_eval_exp e)
      | exp_inr e                => term_inr (symbolic_eval_exp e)
      | exp_list es              => term_list (List.map symbolic_eval_exp es)
      | exp_bvec es              => term_bvec (Vector.map symbolic_eval_exp es)
      | exp_tuple es             => term_tuple (env_map (@symbolic_eval_exp) es)
      | @exp_projtup _ _ e n _ p => term_projtup (symbolic_eval_exp e) n (p := p)
      | exp_union E K e          => term_union E K (symbolic_eval_exp e)
      | exp_record R es          => term_record R (env_map (fun _ => symbolic_eval_exp) es)
      | exp_projrec e rf         => term_projrec (symbolic_eval_exp e) rf
      end%exp.

  Record SepContract (Δ : Ctx (𝑿 * Ty)) (τ : Ty) : Type :=
    MkSepContract
      { sep_contract_logic_variables  : Ctx (𝑺 * Ty);
        sep_contract_localstore       : SymbolicLocalStore Δ sep_contract_logic_variables;
        sep_contract_precondition     : Assertion sep_contract_logic_variables;
        sep_contract_result           : 𝑺;
        sep_contract_postcondition    : Assertion (sep_contract_logic_variables ▻ (sep_contract_result , τ));
      }.

  Arguments MkSepContract : clear implicits.

  Definition SepContractEnv : Type :=
    forall Δ τ (f : 𝑭 Δ τ), option (SepContract Δ τ).
  Definition SepContractEnvEx : Type :=
    forall Δ τ (f : 𝑭𝑿 Δ τ), SepContract Δ τ.

  Section Experimental.

    Definition sep_contract_pun_logvars (Δ : Ctx (𝑿 * Ty)) (Σ : Ctx (𝑺 * Ty)) : Ctx (𝑺 * Ty) :=
      ctx_map (fun '(x,σ) => (𝑿to𝑺 x,σ)) Δ ▻▻ Σ.

    Record SepContractPun (Δ : Ctx (𝑿 * Ty)) (τ : Ty) : Type :=
      MkSepContractPun
        { sep_contract_pun_logic_variables   : Ctx (𝑺 * Ty);
          sep_contract_pun_precondition      : Assertion
                                                 (sep_contract_pun_logvars
                                                    Δ sep_contract_pun_logic_variables);
          sep_contract_pun_result            : 𝑺;
          sep_contract_pun_postcondition     : Assertion
                                                 (sep_contract_pun_logvars Δ
                                                                           sep_contract_pun_logic_variables
                                                                           ▻ (sep_contract_pun_result , τ))
        }.

    Global Arguments MkSepContractPun : clear implicits.

    Definition sep_contract_pun_to_sep_contract {Δ τ} :
      SepContractPun Δ τ -> SepContract Δ τ :=
      fun c =>
        match c with
        | MkSepContractPun _ _ Σ req result ens =>
          MkSepContract
            Δ τ
            (sep_contract_pun_logvars Δ Σ)
            (env_tabulate (fun '(x,σ) xIn =>
                             @term_var
                               (sep_contract_pun_logvars Δ Σ)
                               (𝑿to𝑺 x)
                               σ
                               (inctx_cat (inctx_map (fun '(y,τ) => (𝑿to𝑺 y,τ)) xIn) Σ)))
            req result ens
        end.

    Global Coercion sep_contract_pun_to_sep_contract : SepContractPun >-> SepContract.

  End Experimental.

  Class IHeaplet (L : Type) := {
    is_ISepLogic :> ISepLogic L;
    lpred (p : 𝑷) (ts : Env Lit (𝑷_Ty p)) : L;
    lptsreg  {σ : Ty} (r : 𝑹𝑬𝑮 σ) (t : Lit σ) : L
  }.

  Arguments lpred {L _} p ts.

  Section Contracts.
    Context `{Logic : IHeaplet L}.

    Definition inst_chunk {Σ} (ι : SymInstance Σ) (c : Chunk Σ) : L :=
      match c with
      | chunk_pred p ts => lpred p (inst ι ts)
      | chunk_ptsreg r t => lptsreg r (inst ι t)
      end.

    Fixpoint inst_assertion {Σ} (ι : SymInstance Σ) (a : Assertion Σ) : L :=
      match a with
      | asn_bool b => if inst (A := Lit ty_bool) ι b then emp else lfalse
      | asn_prop p => !!(uncurry_named p ι) ∧ emp
      | asn_eq t1 t2 => !!(inst_term ι t1 = inst_term ι t2) ∧ emp
      | asn_chunk c => inst_chunk ι c
      | asn_if b a1 a2 => if inst (A := Lit ty_bool) ι b then inst_assertion ι a1 else inst_assertion ι a2
      | asn_match_enum E k alts => inst_assertion ι (alts (inst (T := fun Σ => Term Σ _) ι k))
      | asn_sep a1 a2 => inst_assertion ι a1 ✱ inst_assertion ι a2
      | asn_exist ς τ a => ∃ (v : Lit τ), inst_assertion (ι ► (ς∶τ ↦ v)) a
    end%logic.

    Definition inst_contract_localstore {Δ τ} (c : SepContract Δ τ)
      (ι : SymInstance (sep_contract_logic_variables c)) : LocalStore Δ :=
      inst ι (sep_contract_localstore c).

    Definition inst_contract_precondition {Δ τ} (c : SepContract Δ τ)
      (ι : SymInstance (sep_contract_logic_variables c)) : L :=
      inst_assertion ι (sep_contract_precondition c).

    Definition inst_contract_postcondition {Δ τ} (c : SepContract Δ τ)
      (ι : SymInstance (sep_contract_logic_variables c)) (result : Lit τ) :  L :=
        inst_assertion (env_snoc ι (sep_contract_result c,τ) result) (sep_contract_postcondition c).

  End Contracts.

  Arguments inst_assertion {_ _ _} _ _.

End Assertions.

Module Type SymbolicContractKit
       (Import termkit : TermKit)
       (Import progkit : ProgramKit termkit)
       (Import assertkit : AssertionKit termkit progkit).

  Module Export ASS := Assertions termkit progkit assertkit.

  Parameter Inline CEnv   : SepContractEnv.
  Parameter Inline CEnvEx : SepContractEnvEx.

End SymbolicContractKit.
