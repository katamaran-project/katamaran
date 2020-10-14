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
     Syntax.

Import CtxNotations.
Import EnvNotations.

Set Implicit Arguments.

Module Type AssertionKit
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit)
       (Import progkit : ProgramKit typekit termkit).
  Module PM := Programs typekit termkit progkit.
  Export PM.

  (* Predicate names. *)
  Parameter Inline 𝑷  : Set.
  (* Predicate field types. *)
  Parameter Inline 𝑷_Ty : 𝑷 -> Ctx Ty.
  Parameter Inline 𝑷_eq_dec : forall (p : 𝑷) (q : 𝑷), {p = q}+{~ p = q}.

End AssertionKit.

Module Assertions
       (typekit : TypeKit)
       (termkit : TermKit typekit)
       (progkit : ProgramKit typekit termkit)
       (assertkit : AssertionKit typekit termkit progkit).
  Export assertkit.

  Inductive Chunk (Σ : Ctx (𝑺 * Ty)) : Type :=
  | chunk_pred   (p : 𝑷) (ts : Env (Term Σ) (𝑷_Ty p))
  | chunk_ptsreg {σ : Ty} (r : 𝑹𝑬𝑮 σ) (t : Term Σ σ).
  Arguments chunk_pred [_] _ _.

  Inductive Assertion (Σ : Ctx (𝑺 * Ty)) : Type :=
  | asn_bool (b : Term Σ ty_bool)
  | asn_prop (P : abstract_named Lit Σ Prop)
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

  Global Instance sub_chunk : Subst Chunk :=
    fun Σ1 Σ2 ζ c =>
      match c with
      | chunk_pred p ts => chunk_pred p (env_map (fun _ => sub_term ζ) ts)
      | chunk_ptsreg r t => chunk_ptsreg r (sub_term ζ t)
      end.

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
      | exp_var ς                => (δ ‼ ς)%lit
      | exp_lit _ σ l            => term_lit σ l
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
      end.

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

End Assertions.

Module Type SymbolicContractKit
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit)
       (Import progkit : ProgramKit typekit termkit)
       (Import assertkit : AssertionKit typekit termkit progkit).

  Module ASS := Assertions typekit termkit progkit assertkit.
  Export ASS.

  Parameter Inline CEnv   : SepContractEnv.
  Parameter Inline CEnvEx : SepContractEnvEx.

End SymbolicContractKit.
