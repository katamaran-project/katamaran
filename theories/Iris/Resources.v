(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese, Sander Huyghebaert, Steven Keuchel  *)
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

From Equations Require Import
     Equations Signature.

From iris Require Import
     algebra.auth
     algebra.excl
     algebra.gmap
     program_logic.adequacy
     program_logic.weakestpre
     proofmode.tactics.

From Katamaran Require Import
     Prelude
     Semantics.

Require Import Coq.Program.Equality.

Import ctx.notations.
Import env.notations.
Set Implicit Arguments.

Section TransparentObligations.
  Local Set Transparent Obligations.
  (* Derive NoConfusion for SomeReg. *)
  (* Derive NoConfusion for SomeVal. *)
  Derive NoConfusion for iris.algebra.excl.excl.
End TransparentObligations.

Module Type IrisParameters
  (Import B    : Base).

  (* The memGS field will normally always be instantiated to a type class. We
     inline this field, so that instances declared by the library, e.g. the
     [sailGS_memGS] superclass instance below, will always be instances for the
     user-provided class instead of the [memGS] alias. In your client code, you
     should always refer to your typeclass and refrain from using the [memGS]
     aliases completely. *)
  Parameter Inline memGS : gFunctors -> Set.
  Parameter mem_inv : forall `{mG : memGS Σ}, Memory -> iProp Σ.
End IrisParameters.

(* TODO: export, back to module instead of module type *)
Module Type IrisPrelims
    (Import B    : Base)
    (Import PROG : Program B)
    (Import SEM  : Semantics B PROG).

  Import SmallStepNotations.

  Section Language.

    (* IVal designates the values in our language, allowing for succesful
       termination with a value, or failure termination with a string. *)
    Definition IVal (τ : Ty) : Type := Val τ + Val ty.string.

    (* The "expressions" of the LanguageMixin are configurations consisting of a
       statement and a local variable store. *)
    Record Conf (Γ : PCtx) τ : Type :=
      MkConf
        { conf_stm   : Stm Γ τ;
          conf_store : CStore Γ
        }.

    Section TransparentObligations.
      Local Set Transparent Obligations.
      Derive NoConfusion for Conf.
    End TransparentObligations.

    (* The "values" of the LanguageMixin are final configurations consisting of a
       value and a store. We only keep the store around for technical reasons,
       essentially to validate of_to_val. *)
    Section ValConf.
      Local Set Primitive Projections.
      Record ValConf (Γ : PCtx) τ : Type :=
        MkValConf
          { valconf_val   : IVal τ;
            valconf_store : CStore Γ
          }.
    End ValConf.

    Definition of_ival {Γ τ} (v : IVal τ) : Stm Γ τ :=
      match v with
      | inl v => stm_val _ v
      | inr m => stm_fail _ m
      end.

    Definition of_val {Γ} {τ} (v : ValConf Γ τ) : Conf Γ τ :=
      MkConf (of_ival (valconf_val v)) (valconf_store v).

    Definition stm_to_val {Γ τ} (s : Stm Γ τ) : option (IVal τ) :=
      match s with
      | stm_val _ v  => Some (inl v)
      | stm_fail _ m => Some (inr m)
      | _            => None
      end.

    Lemma stm_val_stuck {Γ τ γ1 γ2 μ1 μ2 δ1 δ2} {s1 s2 : Stm Γ τ} :
      ⟨ γ1, μ1, δ1, s1 ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ -> stm_to_val s1 = None.
    Proof. now destruct 1. Qed.

    Lemma stm_to_val_Some_inl {Γ τ} {s : Stm Γ τ} {v : Val τ} :
      stm_to_val s = Some (inl v) ->
      s = stm_val _ v.
    Proof.
      intros H; destruct s; try discriminate; inversion H; subst; auto.
    Qed.

    Lemma stm_to_val_Some_inr {Γ τ} {s : Stm Γ τ} {m : Val ty.string} :
      stm_to_val s = Some (inr m) ->
      s = stm_fail _ m.
    Proof.
      intros H; destruct s; try discriminate; inversion H; subst; auto.
    Qed.

    Lemma stm_to_val_Some_cases {Γ τ} {s : Stm Γ τ} {v : IVal τ} :
      stm_to_val s = Some v ->
      (∃ v', s = stm_val τ v' ∧ v = inl v') ∨ (∃ m, s = stm_fail τ m ∧ v = inr m).
    Proof.
      intros H; destruct s, v; try discriminate; inversion H; subst.
      - left. eexists. split; reflexivity.
      - right. eexists. split; reflexivity.
    Qed.

    Definition stm_to_fail {Γ τ} (s : Stm Γ τ) : option string :=
      match s with
      | stm_fail _ m => Some m
      | _           => None
      end.

    Lemma stm_fail_stuck {Γ τ γ1 γ2 μ1 μ2 δ1 δ2} {s1 s2 : Stm Γ τ} :
      ⟨ γ1, μ1, δ1, s1 ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ -> stm_to_fail s1 = None.
    Proof. now destruct 1. Qed.

    Definition to_val {Γ} {τ} (t : Conf Γ τ) : option (ValConf Γ τ) :=
      match t with
      | MkConf s δ => option.map (fun v => MkValConf v δ) (stm_to_val s)
      end.

    Lemma to_of_val {Γ} {τ} (v : ValConf Γ τ) : to_val (of_val v) = Some v.
    Proof.
      by destruct v as [[] ?].
    Qed.

    Lemma of_to_val {Γ} {τ} (s : Conf Γ τ) v : to_val s = Some v → of_val v = s.
    Proof.
      destruct s as [s δ]; destruct s; try done.
      by intros [= <-].
      by intros [= <-].
    Qed.

    Lemma stm_to_val_of_ival {Γ τ} (v : IVal τ) :
      @stm_to_val Γ τ (of_ival v) = Some v.
    Proof. by destruct v. Qed.

    Lemma stm_to_val_eq {Γ τ} {s : Stm Γ τ} {v : IVal τ} :
      stm_to_val s = Some v ->
      s = of_ival v.
    Proof.
      destruct s, v; try discriminate; intros H; inversion H; subst; auto.
    Qed.

    Definition observation := Empty_set.

    Definition State := prod RegStore Memory.

    Variant prim_step [Γ τ] (c1 : Conf Γ τ) : State -> list Empty_set -> Conf Γ τ -> State -> list (Conf Γ τ) -> Prop :=
      mk_prim_step γ1 γ2 μ1 μ2 (δ2 : CStore Γ) s2 :
        ⟨ γ1, μ1, conf_store c1 , conf_stm c1 ⟩ ---> ⟨ γ2, μ2, δ2, s2 ⟩ ->
        prim_step c1 (γ1 , μ1) nil (MkConf s2 δ2) (γ2 , μ2) nil.

    Lemma val_head_stuck {Γ τ} (e1 : Conf Γ τ) s1 ls e2 s2 {ks} :
      prim_step e1 s1 ls e2 s2 ks -> to_val e1 = None.
    Proof. destruct 1, e1. cbn in H. now destruct H. Qed.

    Lemma microsail_lang_mixin Γ τ : LanguageMixin of_val to_val (@prim_step Γ τ).
    Proof. split; eauto using to_of_val, of_to_val, val_head_stuck. Qed.

    Canonical Structure microsail_lang Γ τ : language := Language (microsail_lang_mixin Γ τ).

    #[export] Instance intoVal_valconf {Γ τ δ v} : IntoVal (MkConf (Γ := Γ) (τ := τ) (stm_val _ v) δ) (MkValConf (inl v) δ).
      intros; eapply of_to_val; by cbn.
    Defined.

    #[export] Instance intoVal_failconf {Γ τ δ m} : IntoVal (MkConf (Γ := Γ) (τ := τ) (stm_fail _ m) δ) (MkValConf (inr m) δ).
      intros; eapply of_to_val; by cbn.
    Defined.

  End Language.

  Section Registers.

    Definition SomeReg : Type := sigT 𝑹𝑬𝑮.
    Definition SomeVal : Type := sigT Val.

    Definition RegStore_to_map (γ : RegStore) : gmap SomeReg (exclR (leibnizO SomeVal)) :=
      list_to_map (K := SomeReg)
                  (fmap (fun x => match x with
                                existT _ r =>
                                  pair (existT _ r) (Excl (existT _ (read_register γ r)))
                              end)
                       (finite.enum (sigT 𝑹𝑬𝑮))).

    Lemma RegStore_to_map_Forall (γ : RegStore) :
      map_Forall (K := SomeReg)
        (fun reg v => match reg with | existT _ reg => Excl (existT _ (read_register γ reg)) = v end)
        (RegStore_to_map γ).
    Proof.
      eapply map_Forall_lookup_2.
      intros [σ r] x eq.
      unfold RegStore_to_map in eq.
      destruct (list_to_map _ !! _) eqn:eq' in eq; inversion eq; subst.
      rewrite <-elem_of_list_to_map in eq'.
      - eapply elem_of_list_fmap_2 in eq'.
        destruct eq' as ([σ' r'] & eq2 & eq3).
        now inversion eq2.
      - rewrite <-list_fmap_compose.
        rewrite (list_fmap_ext _ id).
        + rewrite list_fmap_id.
          eapply finite.NoDup_enum.
        + now intros i [σ' r'].
    Qed.

    Lemma RegStore_to_map_valid (γ : RegStore) :
      valid (RegStore_to_map γ).
    Proof.
      intros [σ r].
      rewrite (elem_of_list_to_map_1' _ _ (Excl (existT _ (read_register γ r))));
        first done.
      - intros y ([y1 y2] & eq & _)%elem_of_list_fmap_2.
        now inversion eq.
      - eapply (elem_of_list_fmap_1 (λ x : SomeReg, let (x0, r0) := x in _) _ (existT σ r)).
        eapply finite.elem_of_enum.
    Qed.

    #[export] Instance eqDec_SomeReg : EqDec SomeReg := 𝑹𝑬𝑮_eq_dec.
    #[export] Instance countable_SomeReg : countable.Countable SomeReg := finite.finite_countable.

    #[export] Instance eqDec_SomeVal : EqDec SomeVal := sigma_eqdec _ _.

    Definition regUR := authR (gmapUR SomeReg (exclR (leibnizO SomeVal))).
    (* Definition regUR' : cmra := *)
    (*   authR (discrete_funUR (A := SomeReg) *)
    (*            (fun '(existT σ r) => excl_auth.excl_authUR (leibnizO (Val σ)))). *)

    Class sailRegGS Σ := SailRegGS {
                            (* ghost variable for tracking state of registers *)
                            reg_inG : inG Σ regUR;
                            reg_gv_name : gname;
                          }.
    #[export] Existing Instance reg_inG.

    Context `{srGS: sailRegGS Σ}.
    Definition reg_pointsTo {τ} (r : 𝑹𝑬𝑮 τ) (v : Val τ) : iProp Σ :=
      own reg_gv_name (◯ {[ existT _ r := Excl (existT _ v) ]}).

    Definition regs_inv (regstore : RegStore) : iProp Σ :=
      (∃ regsmap,
          own reg_gv_name (● regsmap) ∗
          ⌜ map_Forall (K := SomeReg) (A := excl SomeVal) (fun reg v => match reg with | existT _ reg => Excl (existT _ (read_register regstore reg)) = v end ) regsmap ⌝
      )%I.

    Lemma reg_valid regstore {τ} (r : 𝑹𝑬𝑮 τ) (v : Val τ) :
      ⊢ (regs_inv regstore -∗ reg_pointsTo r v -∗ ⌜read_register regstore r = v⌝)%I.
    Proof.
      iDestruct 1 as (regsmap) "[Hregs %]".
      iIntros "Hreg".
      iDestruct (own_valid_2 with "Hregs Hreg") as %[Hl regsv]%auth_both_valid.
      iPureIntro.
      specialize (Hl 0).
      setoid_rewrite (singleton_includedN_l 0 regsmap (existT _ r) _) in Hl.
      destruct Hl as [y [eq1%discrete%leibniz_equiv eq2%cmra_discrete_included_r]];
        auto with typeclass_instances.
      specialize (regsv (existT _ r)).
      rewrite eq1 in regsv.
      destruct y as [y|]; [|inversion regsv].
      setoid_rewrite Excl_included in eq2.
      apply leibniz_equiv in eq2. subst.
      specialize (H (existT _ r) (Excl (existT _ v)) eq1); cbn in H.
      Local Set Equations With UIP.
      by dependent elimination H.
    Qed.

    Lemma regs_inv_update {τ} {r} {v : Val τ} {regsmap : gmapUR SomeReg (exclR (leibnizO SomeVal))} {regstore : RegStore} :
      map_Forall (K := SomeReg) (A := excl SomeVal) (λ r' v', match r' with
                           | existT τ r'' => Excl (existT _ (read_register regstore r'')) = v'
                           end) regsmap ->
      (own reg_gv_name (● <[existT _ r:=Excl (existT _ v)]> regsmap)) -∗ regs_inv (write_register regstore r v).
    Proof.
      iIntros (regseq) "Hownregs".
      iExists (<[existT _ r:=Excl (existT _ v)]> regsmap).
      iFrame.
      iPureIntro.
      apply (map_Forall_lookup_2 _ (<[existT _ r:=Excl (existT _ v)]> regsmap)).
      intros [τ' r'] x eq1.
      destruct (eq_dec_het r r') as [eq2|neq].
      + dependent elimination eq2.
        rewrite lookup_insert in eq1.
        apply (inj Some) in eq1.
        by rewrite <- eq1, (read_write regstore r v).
      + assert (existT _ r ≠ existT _ r') as neq2.
        * intros eq2.
          dependent elimination eq2.
          now apply neq.
        * rewrite (lookup_insert_ne _ _ _ _ neq2) in eq1.
          rewrite (read_write_distinct _ _ neq).
          apply (map_Forall_lookup_1 _ _ _ _ regseq eq1).
    Qed.

    Lemma reg_update regstore {τ} r (v1 v2 : Val τ) :
      regs_inv regstore -∗ reg_pointsTo r v1 ==∗ regs_inv (write_register regstore r v2) ∗ reg_pointsTo r v2.
    Proof.
      iDestruct 1 as (regsmap) "[Hregs %]".
      rewrite /reg_pointsTo.
      iIntros "Hreg".
      iDestruct (own_valid_2 with "Hregs Hreg") as %[Hl%cmra_discrete_included_r regsmapv]%auth_both_valid.
      setoid_rewrite (singleton_included_l regsmap (existT _ r) _) in Hl.
      destruct Hl as [y [eq1%leibniz_equiv eq2]].
      specialize (regsmapv (existT _ r)).
      rewrite eq1 in regsmapv.
      destruct y as [y|]; inversion regsmapv.
      iMod (own_update_2 with "Hregs Hreg") as "Hregs".
      {
        eapply auth_update.
        apply (singleton_local_update regsmap (existT _ r) (Excl y) (Excl (existT _ v1)) (Excl (existT _ v2)) (Excl (existT _ v2)) eq1).
        by eapply exclusive_local_update.
      }
      iDestruct "Hregs" as "[Hregs $]".
      now iApply (regs_inv_update H).
    Qed.

    Import stdpp.list.

    Lemma own_RegStore_to_map_reg_pointsTos {γ : RegStore} {l : list (sigT 𝑹𝑬𝑮)} :
      NoDup l ->
      ⊢ own reg_gv_name (◯ list_to_map (K := SomeReg)
                           (fmap (fun x => match x with existT _ r =>
                                                       pair (existT _ r) (Excl (existT _ (read_register γ r)))
                                        end) l)) -∗
        [∗ list] x ∈ l,
          let (x0, r) := (x : sigT 𝑹𝑬𝑮) in reg_pointsTo r (read_register γ r).
    Proof.
      iIntros (nodups) "Hregs".
      iInduction l as [|[x r]] "IH".
      - now iFrame.
      - rewrite big_sepL_cons. cbn.
        rewrite (insert_singleton_op (A := exclR (leibnizO SomeVal)) (list_to_map (_ <$> l))  (existT x r) (Excl (existT _ (read_register γ r)))).
        rewrite auth_frag_op.
        iPoseProof (own_op with "Hregs") as "[Hreg Hregs]".
        iFrame.
        iApply ("IH" with "[%] [$]").
        + refine (NoDup_cons_1_2 (existT x r) l nodups).
        + destruct (proj1 (NoDup_cons (existT x r) _) nodups) as [notin _].
          refine (not_elem_of_list_to_map_1 _ (existT x r) _).
          rewrite <-list_fmap_compose.
          rewrite (list_fmap_ext _ id).
          now rewrite list_fmap_id.
          now intros i [σ2 r2].
    Qed.

    Lemma own_RegStore_to_regs_inv {γ} : own reg_gv_name (● RegStore_to_map γ) ⊢ regs_inv γ.
    Proof.
      iIntros "Hregs".
      iExists _; iFrame; iPureIntro.
      apply RegStore_to_map_Forall.
    Qed.

  End Registers.
End IrisPrelims.

Module Type IrisResources
  (Import B    : Base)
  (Import PROG : Program B)
  (Import SEM  : Semantics B PROG)
  (Import IPre : IrisPrelims B PROG SEM)
  (Import IP   : IrisParameters B).
  Class sailGS Σ := SailGS { (* resources for the implementation side *)
                       sailGS_invGS : invGS Σ; (* for fancy updates, invariants... *)
                       sailGS_sailRegGS : sailRegGS Σ;

                       (* ghost variable for tracking state of memory cells *)
                       sailGS_memGS : memGS Σ
                     }.
  #[export] Existing Instance sailGS_invGS.
  #[export] Existing Instance sailGS_sailRegGS.

  (* We declare the memGS field as a class so that we can define the
     [sailGS_memGS] field as an instance as well. Currently, the [Existing
     Class] command does not support specifying a locality
     (local/export/global), so it is not clear what the scope of this command
     is. Because [memGS] will be inline on module functor applications, the
     [sailGS_memGS] instance will refer to the user-provided class instead of
     the [memGS] field. *)
  Existing Class memGS.
  #[export] Existing Instance sailGS_memGS.

  #[export] Instance sailGS_irisGS {Γ τ} `{sailGS Σ} : irisGS (microsail_lang Γ τ) Σ := {
    iris_invGS := sailGS_invGS;
    state_interp σ ns κs nt := (regs_inv σ.1 ∗ mem_inv σ.2)%I;
    fork_post _ := True%I; (* no threads forked in sail, so this is fine *)
    num_laters_per_step _ := 0;
    state_interp_mono _ _ _ _ := fupd_intro _ _;
                                                                                }.
  Global Opaque iris_invGS.

  Definition Post {Σ} (Γ : PCtx) (τ : Ty) : Type :=
    IVal τ -> CStore Γ -> iProp Σ.

  Definition lift_cnt {Γ τ σ} (k : Val σ -> Stm Γ τ) (v : IVal σ) : Stm Γ τ :=
    match v with
    | inl v => k v
    | inr m => stm_fail _ m
    end.

End IrisResources.
