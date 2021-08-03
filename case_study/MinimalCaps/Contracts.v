(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel, Dominique Devriese, Sander Huyghebaert  *)
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

From MinimalCaps Require Import
     Machine.

From Coq Require Import
     Program.Tactics
     Strings.String
     ZArith.ZArith
     micromega.Lia.

From Equations Require Import
     Equations.

From MicroSail Require Import
     Sep.Spec
     Symbolic.Mutator
     Syntax.

From MicroSail Require Environment.
From MicroSail Require Sep.Logic.

Set Implicit Arguments.
Import CtxNotations.
Import EnvNotations.
Open Scope string_scope.
Open Scope ctx_scope.
Open Scope Z_scope.

Inductive Predicate : Set :=
  ptsreg
| ptsto
| safe
| subperm
| dummy
.

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for Predicate.

End TransparentObligations.

Derive EqDec for Predicate.

Module Export MinCapsAssertionKit <:
  (AssertionKit MinCapsTermKit MinCapsProgramKit).

  Export MinCapsProgramKit.

  Definition 𝑷 := Predicate.
  Definition 𝑷_Ty (p : 𝑷) : Ctx Ty :=
    match p with
    | ptsreg => [ty_enum regname, ty_word]
    | ptsto => [ty_addr, ty_memval]
    | safe => [ty_word]
    | subperm => [ty_perm, ty_perm]
    | dummy => [ty_cap]
    end.
  Instance 𝑷_eq_dec : EqDec 𝑷 := Predicate_eqdec.
End MinCapsAssertionKit.

Module MinCapsSymbolicContractKit <:
  SymbolicContractKit MinCapsTermKit MinCapsProgramKit MinCapsAssertionKit.
  Module Export ASS := Assertions MinCapsTermKit MinCapsProgramKit MinCapsAssertionKit.

  Local Notation "r '↦' t" := (asn_chunk (chunk_ptsreg r t)) (at level 100).
  Local Notation "p '✱' q" := (asn_sep p q) (at level 150).

  Open Scope env_scope.

  Local Notation "r '↦r' t" := (asn_chunk (chunk_user ptsreg (env_nil ► (ty_enum regname ↦ r) ► (ty_word ↦ t)))) (at level 100).
  Local Notation "a '↦m' t" := (asn_chunk (chunk_user ptsto (env_nil ► (ty_addr ↦ a) ► (ty_int ↦ t)))) (at level 100).
  Local Notation "p '<=ₚ' p'" := (asn_chunk (chunk_user subperm (env_nil ► (ty_perm ↦ p) ► (ty_perm ↦ p')))) (at level 100).
  Local Notation asn_match_option T opt xl alt_inl alt_inr := (asn_match_sum T ty_unit opt xl alt_inl "_" alt_inr).
  Local Notation asn_safe w := (asn_chunk (chunk_user safe (env_nil ► (ty_word ↦ w)))).
  Local Notation asn_csafe c := (asn_chunk (chunk_user safe (env_nil ► (ty_word ↦ (term_inr c))))).
  Local Notation asn_dummy c := (asn_chunk (chunk_user dummy (env_nil ► (ty_cap ↦ c)))).
  Local Notation asn_match_cap c p b e a asn :=
    (asn_match_record
       capability c
       (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
        "cap_permission" p)
        "cap_begin" b)
        "cap_end" e)
        "cap_cursor" a)
       asn).
  Local Notation asn_within_bounds a b e :=
    (asn_formula (formula_bool (term_binop binop_and
                              (term_binop binop_le b a)
                              (term_binop binop_le a e)))).

  (* Arguments asn_prop [_] & _. *)

  (* regInv(r) = ∃ w : word. r ↦ w * safe(w) *)
  Definition regInv {Σ} (r : RegName) (w : string) : Assertion Σ :=
    asn_exist w ty_word
              (term_lit (ty_enum regname) r ↦r (@term_var _ _ _ inctx_zero) ✱
                asn_safe (@term_var _ _ _ inctx_zero)).

  (* regInv(r) = ∃ c : cap. r ↦ c * csafe(c) *)
  Definition regInvCap {Σ} (r : Reg ty_cap) : Assertion Σ :=
    asn_exist "c" ty_cap
              (r ↦ term_var "c" ✱
                 asn_csafe (term_var "c")).

  (* machInv = regInv(r1) * regInv(r2) * regInv(r3) * regInv(r4) * regInvCap(pc) *)
  Definition machInv {Σ} : Assertion Σ :=
    (regInv R0 "w0") ✱ (regInv R1 "w1") ✱ (regInvCap pc).
    (* ✱ (regInv R2 "w2") ✱ (regInv R3 "w3") *)

  (*
     @pre machInv;
     @post machInv;
     τ f(Δ...) *)
  Definition machInv_contract {Δ τ} (localstore : SStore Δ Δ) : SepContract Δ τ :=
    {| sep_contract_logic_variables := Δ;
       sep_contract_localstore      := localstore;
       sep_contract_precondition    := machInv;
       sep_contract_result          := "_";
       sep_contract_postcondition   := machInv;
    |}.

  (* TODO: fix this, should be possible to create localstore that only contains vars from logic vars env? (keep counter to know at which index a term_var is in the env) *)
  (* Print term_var. *)
  (* Fixpoint create_localstore (Δ : PCtx) : SStore Δ Δ := *)
  (*   env_tabulate (fun '(x :: σ) xIn => *)
  (*                   @term_var *)
  (*                     (sep_contract_pun_logvars Δ Δ) *)
  (*                     (𝑿to𝑺 x) *)
  (*                     σ *)
  (*                     (inctx_cat_left Δ (inctx_map (fun '(y :: τ) => (𝑿to𝑺 y::τ)) xIn))). *)

  (* Fixpoint create_localstore (Δ : PCtx) : SStore Δ Δ := *)
  (*   match Δ with *)
  (*   | ε => env_nil *)
  (*   | ε ▻ (n , t) => [@term_var Δ n t {| inctx_at := 0; inctx_valid := ctx_nth_is Δ 0 (n , t) |}]%arg *)
  (*   | Σ ▻ (n , t) => (env_snoc (create_localstore Σ) (n , t) (@term_var _ _ _ inctx_zero ))%arg *)
  (*   end. *)

  Definition SepContractFun {Δ τ} (f : Fun Δ τ) : Type :=
    SepContract Δ τ.

  Definition SepContractFunGhost {Δ} (f : FunGhost Δ) : Type :=
    SepContract Δ ty_unit.

  Definition SepContractFunX {Δ τ} (f : FunX Δ τ) : Type :=
    SepContract Δ τ.

  Definition sep_contract_read_reg : SepContractFun read_reg :=
    {| sep_contract_logic_variables := ["rreg" ∶ ty_enum regname, "w" ∶ ty_word];
       sep_contract_localstore      := [term_var "rreg"]%arg;
       sep_contract_precondition    := term_var "rreg" ↦r term_var "w";
       sep_contract_result          := "result_read_reg";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_read_reg") (term_var "w") ✱
                term_var "rreg" ↦r term_var "w";
    |}.

  Definition sep_contract_read_reg_cap : SepContractFun read_reg_cap :=
    {| sep_contract_logic_variables := ["creg" ∶ ty_enum regname, "w" ∶ ty_word];
       sep_contract_localstore      := [term_var "creg"]%arg;
       sep_contract_precondition    := term_var "creg" ↦r term_var "w";
       sep_contract_result          := "result_read_reg_cap";
       sep_contract_postcondition   :=
         asn_exist "c" ty_cap
                   (asn_eq (term_var "result_read_reg_cap") (term_var "c") ✱
                           asn_eq (term_var "w") (term_inr (term_var "c")) ✱
                           term_var "creg" ↦r (term_var "w"));
    |}.

  Definition sep_contract_read_reg_num : SepContractFun read_reg_num :=
    {| sep_contract_logic_variables := ["nreg" ∶ ty_enum regname, "w" ∶ ty_word];
       sep_contract_localstore      := [term_var "nreg"]%arg;
       sep_contract_precondition    := term_var "nreg" ↦r term_var "w";
       sep_contract_result          := "result_read_reg_num";
       sep_contract_postcondition   :=
         asn_exist "i" ty_int
                   (asn_eq (term_var "result_read_reg_num") (term_var "i") ✱
                           asn_eq (term_var "w") (term_inl (term_var "i")) ✱
                           term_var "nreg" ↦r term_var "w");
    |}.

  Definition sep_contract_write_reg : SepContract ["wreg" ∶ ty_enum regname, "w"  ∶ ty_word] ty_unit :=
    {| sep_contract_logic_variables := ["wreg" ∶ ty_enum regname, "w" ∶ ty_word];
       sep_contract_localstore      := [term_var "wreg", term_var "w"]%arg;
       sep_contract_precondition    := asn_exist "old_word" ty_word (term_var "wreg" ↦r term_var "old_word");
       sep_contract_result          := "result_write_reg";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_write_reg") (term_lit ty_unit tt) ✱
                term_var "wreg" ↦r term_var "w";
    |}.

  Definition sep_contract_next_pc : SepContract ctx_nil ty_cap :=
    {| sep_contract_logic_variables := ["opc" ∶ ty_cap];
       sep_contract_localstore      := env_nil;
       sep_contract_precondition    := pc ↦ term_var "opc";
       sep_contract_result          := "result_next_pc";
       sep_contract_postcondition   :=
         pc ↦ term_var "opc" ✱
            asn_match_cap (term_var "opc") "perm" "beg" "end" "cur"
            (asn_eq
               (term_var "result_next_pc")
               (term_record capability
                            [term_var "perm",
                             term_var "beg",
                             term_var "end",
                             term_binop binop_plus (term_var "cur") (term_lit ty_addr 1)]))
    |}.

  Definition sep_contract_update_pc : SepContract ctx_nil ty_unit :=
    {| sep_contract_logic_variables := ["opc" ∶ ty_cap];
       sep_contract_localstore      := env_nil;
       sep_contract_precondition    := pc ↦ term_var "opc" ✱ asn_csafe (term_var "opc");
       sep_contract_result          := "result_update_pc";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_update_pc") (term_lit ty_unit tt) ✱
                asn_exist "npc" ty_cap
                (pc ↦ term_var "npc" ✱ asn_csafe (term_var "npc"));
    |}.

  Definition sep_contract_add_pc : SepContract ["offset" ∶ ty_int] ty_unit :=
    {| sep_contract_logic_variables := ["opc" ∶ ty_cap, "offset" ∶ ty_int];
       sep_contract_localstore      := [term_var "offset"]%arg;
       sep_contract_precondition    := pc ↦ term_var "opc" ✱ asn_csafe (term_var "opc");
       sep_contract_result          := "result_add_pc";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_add_pc") (term_lit ty_unit tt) ✱
                asn_exist "npc" ty_cap
                (pc ↦ term_var "npc" ✱ asn_csafe (term_var "npc"));
    |}.

  Definition sep_contract_read_mem : SepContract ["c" ∶ ty_cap ] ty_memval :=
    {| sep_contract_logic_variables := ["c" ∶ ty_cap];
       sep_contract_localstore      := [term_var "c"]%arg;
       sep_contract_precondition    := asn_csafe (term_var "c");
       sep_contract_result          := "read_mem_result";
       sep_contract_postcondition   :=
         asn_csafe (term_var "c") ✱ asn_safe (term_var "read_mem_result")
    |}.

  Definition sep_contract_write_mem : SepContract ["c" ∶ ty_cap, "v" ∶ ty_memval ] ty_unit :=
    {| sep_contract_logic_variables := ["c" ∶ ty_cap, "v" ∶ ty_memval];
       sep_contract_localstore      := [term_var "c", term_var "v"]%arg;
       sep_contract_precondition    := asn_safe (term_var "v") ✱ asn_csafe (term_var "c");
       sep_contract_result          := "write_mem_result";
       sep_contract_postcondition   :=
         asn_csafe (term_var "c") ✱ asn_eq (term_var "write_mem_result") (term_lit ty_unit tt);
    |}.

  Definition sep_contract_read_allowed : SepContract ["p" ∶ ty_perm ] ty_bool :=
    {| sep_contract_logic_variables := ["p" ∶ ty_perm];
       sep_contract_localstore      := [term_var "p"]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_read_allowed";
       sep_contract_postcondition   := 
         asn_if (term_var "result_read_allowed")
                (term_lit ty_perm R <=ₚ term_var "p")
                (asn_eq (term_var "result_read_allowed") (term_lit ty_bool false));
    |}.

  Definition sep_contract_write_allowed : SepContract ["p" ∶ ty_perm ] ty_bool :=
    {| sep_contract_logic_variables := ["p" ∶ ty_perm];
       sep_contract_localstore      := [term_var "p"]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_write_allowed";
       sep_contract_postcondition   :=
         asn_if (term_var "result_write_allowed")
                (term_lit ty_perm RW <=ₚ term_var "p")
                (asn_eq (term_var "result_write_allowed") (term_lit ty_bool false));
    |}.

  Definition sep_contract_upper_bound : SepContract ["a" ∶ ty_addr, "e" ∶ ty_addr ] ty_bool :=
    {| sep_contract_logic_variables := ["a" ∶ ty_addr, "e" ∶ ty_addr ];
       sep_contract_localstore      := [term_var "a", term_var "e"]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_upper_bound";
       sep_contract_postcondition   := 
         (asn_eq (term_var "result_upper_bound")
                 (term_binop binop_le (term_var "a") (term_var "e")));
    |}.

  (* 
      @pre true;
      @post ∃ b,e,a,p. c = mkcap(b,e,a,p) ∧ result = (a >= b && (e = none ∨ e = inl e' ∧ e' >= a));
      bool within_bounds(c : capability);
   *)
  Definition sep_contract_within_bounds : SepContract ["c" ∶ ty_cap] ty_bool := 
    {| sep_contract_logic_variables := ["c" ∶ ty_cap];
       sep_contract_localstore      := [term_var "c"]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_within_bounds";
       sep_contract_postcondition   :=
         asn_match_cap (term_var "c") "perm" "b" "e" "a"
                       (asn_eq (term_var "result_within_bounds")
                               (term_binop binop_and
                                           (term_binop binop_le (term_var "b") (term_var "a"))
                                           (term_binop binop_le (term_var "a") (term_var "e"))));
    |}.

  (*
      @pre machInv;
      @post machInv;
      bool exec_jr(lv : lv) *)
  Definition sep_contract_exec_jr : SepContractFun exec_jr :=
    machInv_contract [term_var "lv"]%arg.

  (*
      @pre machInv;
      @post machInv;
      bool exec_jalr(lv1 : lv, lv2 : lv) *)
  Definition sep_contract_exec_jalr : SepContractFun exec_jalr :=
    machInv_contract [term_var "lv1", term_var "lv2"]%arg.

  (*
      @pre machInv;
      @post machInv;
      bool exec_j(offset : Z) *)
  Definition sep_contract_exec_j : SepContractFun exec_j :=
    machInv_contract [term_var "offset"]%arg.

  (*
      @pre machInv;
      @post machInv;
      bool exec_jal(lv : lv, offset : Z) *)
  Definition sep_contract_exec_jal : SepContractFun exec_jal :=
    machInv_contract [term_var "lv", term_var "offset"]%arg.

  (*
      @pre machInv;
      @post machInv;
      bool exec_bnez(lv : lv, immediate : Z) *)
  Definition sep_contract_exec_bnez : SepContractFun exec_bnez :=
    machInv_contract [term_var "lv", term_var "immediate"]%arg.

  (*
      @pre machInv;
      @post machInv;
      bool exec_mv(lv : lv, hv : ty_hv) *)
  Definition sep_contract_exec_mv : SepContractFun exec_mv :=
    machInv_contract [term_var "lv", term_var "hv"]%arg.

  (*
      @pre machInv;
      @post machInv;
      bool exec_ld(lv : lv, hv : memval, immediate : Z) *)
  Definition sep_contract_exec_ld : SepContractFun exec_ld :=
    machInv_contract [term_var "lv", term_var "hv", term_var "immediate"]%arg.

  (*
      @pre machInv;
      @post machInv;
      bool exec_sd(hv : memval, lv : lv, immediate : Z) *)
  Definition sep_contract_exec_sd : SepContractFun exec_sd :=
    machInv_contract [term_var "hv", term_var "lv", term_var "immediate"]%arg.

  (*
      @pre machInv;
      @post machInv;
      bool exec_lea(lv : lv, hv : ty_hv) *)
  Definition sep_contract_exec_lea : SepContractFun exec_lea :=
    machInv_contract [term_var "lv", term_var "hv"]%arg.

  (*
      @pre machInv;
      @post machInv;
      bool exec_restrict(lv : lv, hv : ty_hv) *)
  Definition sep_contract_exec_restrict : SepContractFun exec_restrict :=
    machInv_contract [term_var "lv", term_var "hv"]%arg.

  (*
      @pre machInv;
      @post machInv;
      bool exec_restricti(lv : lv, immediate : Z) *)
  Definition sep_contract_exec_restricti : SepContractFun exec_restricti :=
    machInv_contract [term_var "lv", term_var "immediate"]%arg.

  (*
      @pre machInv;
      @post machInv;
      bool exec_subseg(lv : lv, hv1 hv2 : ty_hv) *)
  Definition sep_contract_exec_subseg : SepContractFun exec_subseg :=
    machInv_contract [term_var "lv", term_var "hv1", term_var "hv2"]%arg.

  (*
      @pre machInv;
      @post machInv;
      bool exec_subsegi(lv : lv, hv : ty_hv, immediate : Z) *)
  Definition sep_contract_exec_subsegi : SepContractFun exec_subsegi :=
    machInv_contract [term_var "lv", term_var "hv", term_var "immediate"]%arg.

  (*
      @pre machInv;
      @post machInv;
      bool exec_addi(lv : lv, hv : hv, immediate : Z) *)
  Definition sep_contract_exec_addi : SepContractFun exec_addi :=
    machInv_contract [term_var "lv", term_var "hv", term_var "immediate"]%arg.

  (*
      @pre machInv;
      @post machInv;
      bool exec_add(lv1 : lv, lv2 : lv, lv3 : lv) *)
  Definition sep_contract_exec_add : SepContractFun exec_add :=
    machInv_contract [term_var "lv1", term_var "lv2", term_var "lv3"]%arg.

  (*
      @pre machInv;
      @post machInv;
      bool exec_sub(lv1 : lv, lv2 : lv, lv3 : lv) *)
  Definition sep_contract_exec_sub : SepContractFun exec_sub :=
    machInv_contract [term_var "lv1", term_var "lv2", term_var "lv3"]%arg.

  (*
      @pre machInv;
      @post machInv;
      bool exec_slt(lv1 : lv, lv2 : lv, lv3 : lv) *)
  Definition sep_contract_exec_slt : SepContractFun exec_slt :=
    machInv_contract [term_var "lv1", term_var "lv2", term_var "lv3"]%arg.

  (*
      @pre machInv;
      @post machInv;
      bool exec_slti(lv : lv, hv : hv, immediate : Z) *)
  Definition sep_contract_exec_slti : SepContractFun exec_slti :=
    machInv_contract [term_var "lv", term_var "hv", term_var "immediate"]%arg.

  (*
      @pre machInv;
      @post machInv;
      bool exec_sltu(lv1 : lv, lv2 : lv, lv3 : lv) *)
  Definition sep_contract_exec_sltu : SepContractFun exec_sltu :=
    machInv_contract [term_var "lv1", term_var "lv2", term_var "lv3"]%arg.

  (*
      @pre machInv;
      @post machInv;
      bool exec_sltiu(lv : lv, hv : hv, immediate : Z) *)
  Definition sep_contract_exec_sltiu : SepContractFun exec_sltiu :=
    machInv_contract [term_var "lv", term_var "hv", term_var "immediate"]%arg.

  (*
      @pre true;
      @post true;
      int perm_to_bits(p : perm) *)
  Definition sep_contract_perm_to_bits : SepContractFun perm_to_bits :=
    {| sep_contract_logic_variables := ["p" ∶ ty_perm];
       sep_contract_localstore      := [term_var "p"]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result";
       sep_contract_postcondition   := asn_true;
    |}.

  (*
      @pre true;
      @post true;
      int perm_from_bits(i : Z) *)
  Definition sep_contract_perm_from_bits : SepContractFun perm_from_bits :=
    {| sep_contract_logic_variables := ["i" ∶ ty_int];
       sep_contract_localstore      := [term_var "i"]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result";
       sep_contract_postcondition   := asn_true;
    |}.

  (*
      @pre true;
      @post true;
      int abs(i : int) *)
  Definition sep_contract_abs : SepContractFun abs :=
    {| sep_contract_logic_variables := ["i" ∶ ty_int];
       sep_contract_localstore      := [term_var "i"]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result";
       sep_contract_postcondition   := asn_true;
    |}.

  (*
      @pre true;
      @post if p <= p' then (result = true ✱ p ≤ p') else result = false;
      int is_sub_perm(p : perm, p' : perm) *)
  Definition sep_contract_is_sub_perm : SepContractFun is_sub_perm :=
    {| sep_contract_logic_variables := ["p" ∶ ty_perm, "p'" ∶ ty_perm];
       sep_contract_localstore      := [term_var "p", term_var "p'"]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_is_sub_perm";
       sep_contract_postcondition   :=
         asn_if (term_var "result_is_sub_perm")
                (term_var "p" <=ₚ term_var "p'")
                (asn_eq (term_var "result_is_sub_perm") (term_lit ty_bool false));
    |}.

  (*
      @pre true;
      @post result = (b ≤ b' && e' ≤ e) ;
      bool is_within_range(b' e' b e : Addr) *)
  Definition sep_contract_is_within_range : SepContractFun is_within_range :=
    {| sep_contract_logic_variables := ["b'" ∶ ty_addr, "e'" ∶ ty_addr,
                                        "b" ∶ ty_addr, "e" ∶ ty_addr];
       sep_contract_localstore      := [term_var "b'", term_var "e'", term_var "b", term_var "e"]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_is_within_range";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_is_within_range")
                (term_binop binop_and
                            (term_binop binop_le (term_var "b") (term_var "b'"))
                            (term_binop binop_le (term_var "e'") (term_var "e")))
    |}.
  
  (*
      @pre machInv;
      @post machInv;
      bool exec_isptr(lv1 : lv, lv2 : lv) *)
  Definition sep_contract_exec_isptr : SepContractFun exec_isptr :=
    machInv_contract [term_var "lv1", term_var "lv2"]%arg.

  (*
      @pre machInv;
      @post machInv;
      bool exec_getp(lv1 : lv, lv2 : lv) *)
  Definition sep_contract_exec_getp : SepContractFun exec_getp :=
    machInv_contract [term_var "lv1", term_var "lv2"]%arg.

  (*
      @pre machInv;
      @post machInv;
      bool exec_getb(lv1 : lv, lv2 : lv) *)
  Definition sep_contract_exec_getb : SepContractFun exec_getb :=
    machInv_contract [term_var "lv1", term_var "lv2"]%arg.

  (*
      @pre machInv;
      @post machInv;
      bool exec_gete(lv1 : lv, lv2 : lv) *)
  Definition sep_contract_exec_gete : SepContractFun exec_gete :=
    machInv_contract [term_var "lv1", term_var "lv2"]%arg.

  (*
      @pre machInv;
      @post machInv;
      bool exec_geta(lv1 : lv, lv2 : lv) *)
  Definition sep_contract_exec_geta : SepContractFun exec_geta :=
    machInv_contract [term_var "lv1", term_var "lv2"]%arg.

  (* @pre machInv;
     @post machInv;
     bool exec_fail *)
  Definition sep_contract_exec_fail : SepContractFun exec_fail :=
    machInv_contract env_nil.

  (* @pre machInv;
     @post machInv;
     bool exec_ret *)
  Definition sep_contract_exec_ret : SepContractFun exec_ret :=
    machInv_contract env_nil.

  (*
      @pre machInv;
      @post machInv;
      bool exec_instr(i : instr) *)
  Definition sep_contract_exec_instr : SepContractFun exec_instr :=
    machInv_contract [term_var "i"]%arg.

  (*
      @pre machInv;
      @post machInv;
      bool exec *)
  Definition sep_contract_exec : SepContractFun exec :=
    machInv_contract env_nil.

  (*
      @pre machInv;
      @post machInv;
      unit loop *)
  Definition sep_contract_loop : SepContractFun loop :=
    machInv_contract env_nil.

  Definition CEnv : SepContractEnv :=
    fun Δ τ f =>
      match f with
      | read_allowed    => Some sep_contract_read_allowed
      | write_allowed   => Some sep_contract_write_allowed
      | upper_bound     => Some sep_contract_upper_bound
      | within_bounds   => Some sep_contract_within_bounds
      | read_reg        => Some sep_contract_read_reg
      | read_reg_cap    => Some sep_contract_read_reg_cap
      | read_reg_num    => Some sep_contract_read_reg_num
      | write_reg       => Some sep_contract_write_reg
      | next_pc         => Some sep_contract_next_pc
      | add_pc          => Some sep_contract_add_pc
      | update_pc       => Some sep_contract_update_pc
      | read_mem        => Some sep_contract_read_mem
      | write_mem       => Some sep_contract_write_mem
      | perm_to_bits    => Some sep_contract_perm_to_bits
      | perm_from_bits  => Some sep_contract_perm_from_bits
      | is_sub_perm     => Some sep_contract_is_sub_perm
      | is_within_range => Some sep_contract_is_within_range
      | abs             => Some sep_contract_abs
      | exec_jr         => Some sep_contract_exec_jr
      | exec_jalr       => Some sep_contract_exec_jalr
      | exec_j          => Some sep_contract_exec_j
      | exec_jal        => Some sep_contract_exec_jal
      | exec_bnez       => Some sep_contract_exec_bnez
      | exec_mv         => Some sep_contract_exec_mv
      | exec_ld         => Some sep_contract_exec_ld
      | exec_sd         => Some sep_contract_exec_sd
      | exec_lea        => Some sep_contract_exec_lea
      | exec_restrict   => Some sep_contract_exec_restrict
      | exec_restricti  => Some sep_contract_exec_restricti
      | exec_subseg     => Some sep_contract_exec_subseg
      | exec_subsegi    => Some sep_contract_exec_subsegi
      | exec_addi       => Some sep_contract_exec_addi
      | exec_add        => Some sep_contract_exec_add
      | exec_sub        => Some sep_contract_exec_sub
      | exec_slt        => Some sep_contract_exec_slt
      | exec_slti       => Some sep_contract_exec_slti
      | exec_sltu       => Some sep_contract_exec_sltu
      | exec_sltiu      => Some sep_contract_exec_slti
      | exec_isptr      => Some sep_contract_exec_isptr
      | exec_getp       => Some sep_contract_exec_getp
      | exec_getb       => Some sep_contract_exec_getb
      | exec_gete       => Some sep_contract_exec_gete
      | exec_geta       => Some sep_contract_exec_geta
      | exec_fail       => Some sep_contract_exec_fail
      | exec_ret        => Some sep_contract_exec_ret
      | exec_instr      => Some sep_contract_exec_instr
      | exec            => Some sep_contract_exec
      | loop            => Some sep_contract_loop
      | _               => None
      end.

  Lemma linted_cenv :
    forall Δ τ (f : Fun Δ τ),
      match CEnv f with
      | Some c => Linted c
      | None   => True
      end.
  Proof. intros ? ? []; try constructor. Qed.

  Definition sep_contract_open_ptsreg : SepContractFunGhost open_ptsreg :=
    {| sep_contract_logic_variables := [ "reg" ∶ ty_enum regname, "w" ∶ ty_word];
       sep_contract_localstore      := [term_var "reg"]%arg;
       sep_contract_precondition    := term_var "reg" ↦r term_var "w";
       sep_contract_result          := "result";
       sep_contract_postcondition   :=
         asn_match_enum
           regname (term_var "reg")
           (fun k => match k with
                     | R0 => reg0 ↦ term_var "w"
                     | R1 => reg1 ↦ term_var "w"
                     (* | R2 => reg2 ↦ term_var "w"
                     | R3 => reg3 ↦ term_var "w" *)
                     end)
    |}.

  (* TODO: add persistent predicates? *)
  Definition sep_contract_duplicate_safe : SepContractFunGhost duplicate_safe :=
    {| sep_contract_logic_variables := ["w" ∶ ty_word];
       sep_contract_localstore      := [term_var "w"]%arg;
       sep_contract_precondition    := asn_safe (term_var "w");
       sep_contract_result          := "result_duplicate_safe";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_duplicate_safe") (term_lit ty_unit tt) ✱
         asn_safe (term_var "w") ✱
         asn_safe (term_var "w")
    |}.

  Definition sep_contract_safe_move_cursor : SepContractFunGhost safe_move_cursor :=
    let Σ : LCtx := ["p" ∶ ty_perm, "b" ∶ ty_addr, "e" ∶ ty_addr, "a" ∶ ty_addr, "a'" ∶ ty_addr]%ctx in
    let c  : Term Σ _ := term_record capability [term_var "p", term_var "b", term_var "e", term_var "a"] in
    let c' : Term Σ _ := term_record capability [term_var "p", term_var "b", term_var "e", term_var "a'"] in
    {| sep_contract_logic_variables := Σ;
       sep_contract_localstore      := [c', c]%arg;
       sep_contract_precondition    := asn_csafe c;
       sep_contract_result          := "result_csafe_move_cursor";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_csafe_move_cursor") (term_lit ty_unit tt) ✱
         asn_csafe (sub_term c sub_wk1) ✱
         asn_csafe (sub_term c' sub_wk1);
    |}.

  (*
    @pre c = mkcap(p,b,e,a) ✱ c' = mkcap(p',b,e,a) ✱ csafe(c) ✱ p' ≤ p
    @post csafe(c) ✱ csafe(c')
    unit csafe_sub_perm(c : capability, c' : capability);
   *)
  Definition sep_contract_safe_sub_perm : SepContractFunGhost safe_sub_perm :=
    let Σ : LCtx := ["p" ∶ ty_perm, "p'" ∶ ty_perm, "b" ∶ ty_addr, "e" ∶ ty_addr, "a" ∶ ty_addr]%ctx in
    let c  : Term Σ _ := term_record capability [term_var "p", term_var "b", term_var "e", term_var "a"] in
    let c' : Term Σ _ := term_record capability [term_var "p'", term_var "b", term_var "e", term_var "a"] in
    {| sep_contract_logic_variables := Σ;
       sep_contract_localstore      := [c', c]%arg;
       sep_contract_precondition    :=
         asn_csafe c ✱ term_var "p'" <=ₚ term_var "p";
       sep_contract_result          := "result_csafe_sub_perm";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_csafe_sub_perm") (term_lit ty_unit tt) ✱
         asn_csafe (sub_term c sub_wk1) ✱
         asn_csafe (sub_term c' sub_wk1);
    |}.

  (*
    @pre c = mkcap(p,b,e,a) ✱ c' = mkcap(p,b',e',a) ✱ csafe(c) ✱ b ≤ b' ✱ e' ≤ e
    @post csafe(c) ✱ csafe(c')
    unit csafe_within_range(c' : capability, c : capability);
   *)
  Definition sep_contract_safe_within_range : SepContractFunGhost safe_within_range :=
    let Σ : LCtx := ["p" ∶ ty_perm, "b" ∶ ty_addr, "b'" ∶ ty_addr, "e" ∶ ty_addr, "e'" ∶ ty_addr, "a" ∶ ty_addr]%ctx in
    let c  : Term Σ _ := term_record capability [term_var "p", term_var "b", term_var "e", term_var "a"] in
    let c' : Term Σ _ := term_record capability [term_var "p", term_var "b'", term_var "e'", term_var "a"] in
    {| sep_contract_logic_variables := Σ;
       sep_contract_localstore      := [c', c]%arg;
       sep_contract_precondition    :=
         asn_csafe c ✱
         asn_dummy c' ✱
         asn_formula
         (formula_bool
            (term_binop binop_and
                        (term_binop binop_le (term_var "b") (term_var "b'"))
                        (term_binop binop_le (term_var "e'") (term_var "e"))));
       sep_contract_result          := "result_csafe_within_range";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_csafe_within_range") (term_lit ty_unit tt) ✱
         asn_csafe (sub_term c sub_wk1) ✱
         asn_csafe (sub_term c' sub_wk1);
    |}.

  Definition sep_contract_sub_perm : SepContractFunGhost sub_perm :=
    {| sep_contract_logic_variables := ["p" ∶ ty_perm, "p'" ∶ ty_perm];
       sep_contract_localstore      := [term_var "p", term_var "p'"]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_sub_perm";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_sub_perm") (term_lit ty_unit tt) ✱
         asn_match_enum permission (term_var "p")
                        (fun p => match p with
                               | O => term_var "p" <=ₚ term_var "p'"
                               | R => asn_match_enum permission (term_var "p'")
                                                    (fun p' => match p' with
                                                            | O => asn_true
                                                            | _ => term_var "p" <=ₚ term_var "p'"
                                                            end)
                               | RW => asn_match_enum permission (term_var "p'")
                                                    (fun p' => match p' with
                                                            | RW => term_var "p" <=ₚ term_var "p'"
                                                            | _ => asn_true
                                                            end)
                               end);
    |}.

  (*
    @pre true
    @post safe(i)
    unit int_safe(i : int);
   *)
  Definition sep_contract_int_safe : SepContractFunGhost int_safe :=
    {| sep_contract_logic_variables := ["i" ∶ ty_int];
       sep_contract_localstore      := [term_var "i"]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "result_int_safe";
       sep_contract_postcondition   :=
         asn_eq (term_var "result_int_safe") (term_lit ty_unit tt) ✱
                asn_safe (term_inl (term_var "i"));
    |}.

  Definition regtag_to_reg (R : RegName) : Reg ty_word :=
    match R with
    | R0 => reg0
    | R1 => reg1
    (* | R2 => reg2
    | R3 => reg3 *)
    end.

  Definition sep_contract_close_ptsreg (r : RegName) : SepContractFunGhost (close_ptsreg r) :=
    {| sep_contract_logic_variables := ["w" ∶ ty_word];
       sep_contract_localstore      := env_nil;
       sep_contract_precondition    := regtag_to_reg r ↦ term_var "w";
       sep_contract_result          := "_";
       sep_contract_postcondition   := term_enum regname r ↦r term_var "w"
    |}.

  Definition sep_contract_rM : SepContractFunX rM :=
    {| sep_contract_logic_variables := ["address" ∶ ty_addr, "p" ∶ ty_perm, "b" ∶ ty_addr, "e" ∶ ty_addr];
       sep_contract_localstore      := [term_var "address"]%arg;
       sep_contract_precondition    :=
         asn_csafe (term_record capability
                            [term_var "p",
                             term_var "b",
                             term_var "e",
                             term_var "address"]) ✱
                   term_lit ty_perm R <=ₚ term_var "p" ✱
                   asn_within_bounds (term_var "address") (term_var "b") (term_var "e");
       sep_contract_result          := "rM_result";
       sep_contract_postcondition   :=
         asn_csafe (term_record capability
                            [term_var "p",
                             term_var "b",
                             term_var "e",
                             term_var "address"])
           ✱ asn_safe (term_var "rM_result")
    |}.

  Definition sep_contract_wM : SepContractFunX wM :=
    {| sep_contract_logic_variables := ["address" ∶ ty_addr, "new_value" ∶ ty_memval, "p" ∶ ty_perm, "b" ∶ ty_addr, "e" ∶ ty_addr];
       sep_contract_localstore      := [term_var "address", term_var "new_value"]%arg;
       sep_contract_precondition    :=
         asn_safe (term_var "new_value")
                  ✱ asn_csafe (term_record capability
                                           [term_var "p",
                                            term_var "b",
                                            term_var "e",
                                            term_var "address"])
                  ✱ term_lit ty_perm RW <=ₚ term_var "p"
                  ✱ asn_within_bounds (term_var "address") (term_var "b") (term_var "e");
       sep_contract_result          := "wM_result";
       sep_contract_postcondition   :=
         asn_csafe (term_record capability
                            [term_var "p",
                             term_var "b",
                             term_var "e",
                             term_var "address"])
           ✱ asn_eq (term_var "wM_result") (term_lit ty_unit tt)
    |}.

  Definition sep_contract_dI : SepContractFunX dI :=
    {| sep_contract_logic_variables := ["code" ∶ ty_int];
       sep_contract_localstore      := [term_var "code"]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "_";
       sep_contract_postcondition   := asn_true;
    |}.

  Definition sep_contract_gen_dummy : SepContractFunGhost gen_dummy :=
    {| sep_contract_logic_variables := ["c" ∶ ty_cap];
       sep_contract_localstore      := [term_var "c"]%arg;
       sep_contract_precondition    := asn_true;
       sep_contract_result          := "_";
       sep_contract_postcondition   := asn_dummy (term_var "c");
    |}.

  Definition CEnvEx : SepContractEnvEx :=
    fun Δ τ f =>
      match f with
      | rM => sep_contract_rM
      | wM => sep_contract_wM
      | dI => sep_contract_dI
      | @ghost _ f =>
        match f in FunGhost Δ return SepContract Δ ty_unit with
        | open_ptsreg            => sep_contract_open_ptsreg
        | close_ptsreg r         => sep_contract_close_ptsreg r
        | duplicate_safe         => sep_contract_duplicate_safe
        | safe_move_cursor       => sep_contract_safe_move_cursor
        | safe_sub_perm          => sep_contract_safe_sub_perm
        | safe_within_range      => sep_contract_safe_within_range
        | int_safe               => sep_contract_int_safe
        | sub_perm               => sep_contract_sub_perm
        | gen_dummy              => sep_contract_gen_dummy
        end
      end.

  Lemma linted_cenvex :
    forall Δ τ (f : FunX Δ τ),
      Linted (CEnvEx f).
  Proof.
    intros ? ? []; try constructor.
    destruct f; try constructor.
  Qed.

End MinCapsSymbolicContractKit.

Module MinCapsMutators :=
  Mutators
    MinCapsTermKit
    MinCapsProgramKit
    MinCapsAssertionKit
    MinCapsSymbolicContractKit.
Import MinCapsMutators.
Import SMut.

Local Ltac solve :=
  repeat
    (repeat
       match goal with
       | H: _ /\ _ |- _ => destruct H
       | H: Empty_set |- _ => destruct H
       | |- forall _, _ => cbn [Lit snd]; intro
       | |- False \/ _ =>  right
       | |- _ \/ False =>  left
       | |- _ /\ _ => constructor
       | |- VerificationCondition _ =>
         constructor;
         cbv [SPath.safe env_remove env_lookup inctx_case_snoc eval_binop is_true
              inst instantiate_term instantiate_formula inst_term inst_formula Env_rect];
         cbn
       | |- Obligation _ _ _ => constructor; cbn
       | |- Debug _ _ => constructor
       | |- Debug _ True \/ _ => left
       | |- (_ \/ _) \/ _ => rewrite or_assoc
       | |- context[Z.leb ?x ?y] =>
         destruct (Z.leb_spec x y)
       end;
     cbn [List.length andb is_true Lit snd];
     subst; try congruence; try lia;
     auto
    ).

Local Notation "r '↦' t" := (chunk_ptsreg r t) (at level 100, only printing).
Local Notation "r '↦r' t" := (chunk_user ptsreg (env_nil ► (ty_enum regname ↦ r) ► (ty_word ↦ t))) (at level 100, only printing).
Local Notation "a '↦m' t" := (chunk_user ptsto (env_nil ► (ty_addr ↦ a) ► (ty_int ↦ t))) (at level 100, only printing).
Local Notation "p '✱' q" := (asn_sep p q) (at level 150).
Local Notation safew w := (chunk_user safe (env_nil ► (ty_word ↦ w))).
Local Notation asn_csafe c := (asn_chunk (chunk_user safe (env_nil ► (ty_word ↦ (term_inr c))))).
Local Notation asn_dummy c := (asn_chunk (chunk_user dummy (env_nil ► (ty_cap ↦ c)))).
Local Notation asn_match_cap c p b e a asn :=
(asn_match_record
    capability c
    (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
    "cap_permission" p)
    "cap_begin" b)
    "cap_end" e)
    "cap_cursor" a)
    asn).
Local Notation asn_within_bounds a b e :=
  (asn_formula (formula_bool (term_binop binop_and
                                         (term_binop binop_le b a)
                                         (term_binop binop_le a e)))).

Definition ValidContract {Δ τ} (f : Fun Δ τ) : Prop :=
  match CEnv f with
  | Some c => ValidContractReflect c (Pi f)
  | None => False
  end.

(* TODO: remove this debugging contract and function *)
(* pre: csafe(c) ∧ within_range(b', e', b, e)
   post: csafe(c')
   unit to_debug(c', c : Cap) *)
Definition sep_contract_to_debug : SepContract ["c'" ∶ ty_cap, "c" ∶ ty_cap] ty_unit :=
  let Σ : LCtx := ["p" ∶ ty_perm, "b" ∶ ty_addr, "b'" ∶ ty_addr, "e" ∶ ty_addr, "e'" ∶ ty_addr, "a" ∶ ty_addr]%ctx in
  let c  : Term Σ _ := term_record capability [term_var "p", term_var "b", term_var "e", term_var "a"] in
  let c' : Term Σ _ := term_record capability [term_var "p", term_var "b'", term_var "e'", term_var "a"] in
  {| sep_contract_logic_variables := Σ;
     sep_contract_localstore      := [c', c]%arg;
     sep_contract_precondition    :=
         asn_csafe c ✱
         asn_formula
         (formula_bool
            (term_binop binop_and
                        (term_binop binop_le (term_var "b") (term_var "b'"))
                        (term_binop binop_le (term_var "e'") (term_var "e"))));
     sep_contract_result          := "result";
     sep_contract_postcondition   :=
       asn_eq (term_var "result") (term_lit ty_unit tt) ✱
              asn_csafe (sub_term c sub_wk1) ✱
              asn_csafe (sub_term c' sub_wk1);
  |}.

Definition fun_to_debug : Stm ["c'" ∶ ty_cap, "c" ∶ ty_cap] ty_unit :=
  use lemma gen_dummy [exp_var "c'"] ;;
  use lemma safe_within_range [exp_var "c'", exp_var "c"] ;;
  stm_lit ty_unit tt.

Lemma valid_contract_to_debug : ValidContractReflect sep_contract_to_debug fun_to_debug.
Proof. (* compute - [SPath.prune]. *) reflexivity. Qed.

Lemma valid_contract_read_reg : ValidContract read_reg.
Proof. Time reflexivity. Qed.

Lemma valid_contract_read_reg_cap : ValidContract read_reg_cap.
Proof. Time reflexivity. Qed.

Lemma valid_contract_read_reg_num : ValidContract read_reg_num.
Proof. Time reflexivity. Qed.

Lemma valid_contract_write_reg : ValidContract write_reg.
Proof. Time reflexivity. Qed.

Lemma valid_contract_next_pc : ValidContract next_pc.
Proof. Time reflexivity. Qed.

Lemma valid_contract_add_pc : ValidContract add_pc.
Proof. Time reflexivity. Qed.

Lemma valid_contract_update_pc : ValidContract update_pc.
Proof. Time reflexivity. Qed.

Lemma valid_contract_read_mem : ValidContract read_mem.
Proof. Time reflexivity. Qed.

Lemma valid_contract_write_mem : ValidContract write_mem.
Proof. Time reflexivity. Qed.

Lemma valid_contract_read_allowed : ValidContract read_allowed.
Proof. Time reflexivity. Qed.

Lemma valid_contract_write_allowed : ValidContract write_allowed.
Proof. Time reflexivity. Qed.

Lemma valid_contract_upper_bound : ValidContract upper_bound.
Proof. Time reflexivity. Qed.

Lemma valid_contract_within_bounds : ValidContract within_bounds.
Proof. Time reflexivity. Qed.

Lemma valid_contract_perm_to_bits : ValidContract perm_to_bits.
Proof. Time reflexivity. Qed.

Lemma valid_contract_perm_from_bits : ValidContract perm_from_bits.
Proof. Time reflexivity. Qed.

Lemma valid_contract_is_sub_perm : ValidContract is_sub_perm.
Proof. Time reflexivity. Qed.

Lemma valid_contract_is_within_range : ValidContract is_within_range.
Proof. Time reflexivity. Qed.

Lemma valid_contract_abs : ValidContract abs.
Proof. Time reflexivity. Qed.

Lemma valid_contract_exec_jr : ValidContract exec_jr.
Proof. Time reflexivity. Qed.

Lemma valid_contract_exec_j : ValidContract exec_j.
Proof. Time reflexivity. Qed.

Lemma valid_contract_exec_jal : ValidContract exec_jal.
Proof. Time reflexivity. Qed.

Lemma valid_contract_exec_jalr : ValidContract exec_jalr.
Proof. Time reflexivity. Qed.

(*
Ltac debug_satisfy_forget_post :=
  match goal with
  | |- outcome_satisfy ?o ?P =>
    let x := fresh "POST" in
    generalize P; intros x
  end.

Ltac debug_satisfy_remember_post :=
  match goal with
  | |- outcome_satisfy ?o ?P =>
    let x := fresh "POST" in
    remember P as x
  end.

Ltac debug_satisfy_eval_cbn_inputs :=
  match goal with
  | |- outcome_satisfy (?f ?Σ ?ζ ?s) ?P =>
    let Σ' := eval cbn in Σ in
    let ζ' := eval cbn in ζ in
    let s' := eval cbn in s in
    change_no_check (outcome_satisfy (f Σ' ζ' s') P)
  end.

Ltac debug_satisfy_eval_cbv :=
  match goal with
  | |- outcome_satisfy ?o ?P =>
    let o' := eval cbv - [NamedEnv Lit Error] in o in
    change_no_check (outcome_satisfy o' P); cbn [outcome_satisfy]
  end.

Close Scope exp.
Close Scope env.
*)

Lemma valid_contract_exec_bnez : ValidContract exec_bnez.
Proof. Time reflexivity. Qed.

Lemma valid_contract_exec_mv : ValidContract exec_mv.
Proof. Time reflexivity. Qed.

Lemma valid_contract_exec_ld : ValidContract exec_ld.
Proof. Time reflexivity. Qed.

Lemma valid_contract_exec_sd : ValidContract exec_sd.
Proof. Time reflexivity. Qed.

Lemma valid_contract_exec_lea : ValidContract exec_lea.
Proof. Time reflexivity. Qed.

Lemma valid_contract_exec_restrict : ValidContract exec_restrict.
Proof. Time reflexivity. Qed.

Lemma valid_contract_exec_restricti : ValidContract exec_restricti.
Proof. Time reflexivity. Qed.

Lemma valid_contract_exec_subseg : ValidContract exec_subseg.
Proof. Time reflexivity. Qed.

Lemma valid_contract_exec_subsegi : ValidContract exec_subsegi.
Proof. Time reflexivity. Qed.

Lemma valid_contract_exec_addi : ValidContract exec_addi.
Proof. Time reflexivity. Qed.

Lemma valid_contract_exec_add : ValidContract exec_add.
Proof. Time reflexivity. Qed.

Lemma valid_contract_exec_sub : ValidContract exec_sub.
Proof. Time reflexivity. Qed.

Lemma valid_contract_exec_slt : ValidContract exec_slt.
Proof. Time reflexivity. Qed.

Lemma valid_contract_exec_slti : ValidContract exec_slti.
Proof. Time reflexivity. Qed.

Lemma valid_contract_exec_sltu : ValidContract exec_sltu.
Proof. Time reflexivity. Qed.

Lemma valid_contract_exec_sltiu : ValidContract exec_sltiu.
Proof. Time reflexivity. Qed.

Lemma valid_contract_exec_isptr : ValidContract exec_isptr.
Proof. Time reflexivity. Qed.

Lemma valid_contract_exec_getp : ValidContract exec_getp.
Proof. Time reflexivity. Qed.

Lemma valid_contract_exec_getb : ValidContract exec_getb.
Proof. Time reflexivity. Qed.

Lemma valid_contract_exec_gete : ValidContract exec_gete.
Proof. Time reflexivity. Qed.

Lemma valid_contract_exec_geta : ValidContract exec_geta.
Proof. Time reflexivity. Qed.

Lemma valid_contract_exec_fail : ValidContract exec_fail.
Proof. Time reflexivity. Qed.

Lemma valid_contract_exec_ret : ValidContract exec_ret.
Proof. Time reflexivity. Qed.

Lemma valid_contract_exec_instr : ValidContract exec_instr.
Proof. Time reflexivity. Qed.

Definition debug_config : Config :=
  {| config_debug_function _ _ f :=
       match f with
       | read_mem => true
       | _        => false
       end
  |}.

Lemma valid_contract_exec : ValidContract MinCapsTermKit.exec.
Proof. Time reflexivity. Qed.

Lemma valid_contract_loop : ValidContract loop.
Proof. Time reflexivity. Qed.
