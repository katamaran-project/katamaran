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

From Equations Require Import
     Equations.
From Katamaran Require Import
     Context
     Environment
     Notations
     Prelude
     Syntax.BinOps
     Syntax.Terms
     Syntax.TypeDecl
     Syntax.Variables
     Tactics.

Import ctx.notations.
Import env.notations.
Import option.
Import option.notations.

Local Set Implicit Arguments.

Module Type GenOccursCheckOn
  (Import TY : Types)
  (Import TM : TermsOn TY).

  Local Notation LCtx := (NCtx LVar Ty).

  Class SubstUniv (Sb : LCtx -> LCtx -> Type) :=
    MkSubstUniv {
        initSU : forall {Σ}, Sb [ctx] Σ
      ; transSU : forall {Σ1 Σ2 Σ3}, Sb Σ1 Σ2 -> Sb Σ2 Σ3 -> Sb Σ1 Σ3
      ; interpSU : forall {Σ1 Σ2}, Sb Σ1 Σ2 -> Sub Σ1 Σ2
      }.

  Class SubstSU (Sb : LCtx -> LCtx -> Type) (T : LCtx -> Type) :=
    substSU : forall {Σ1 Σ2}, T Σ1 -> Sb Σ1 Σ2 -> T Σ2.

  #[export] Instance substSubstSU `{SubstUniv Sb} `{Subst T} : SubstSU Sb T :=
    fun {Σ1 Σ2} t σ => subst t (interpSU σ).

  Class SubstUnivLaws Sb `{SubstUniv Sb} :=
    interpTransSU : forall {Σ1 Σ2 Σ3} (σ1 : Sb Σ1 Σ2) (σ2 : Sb Σ2 Σ3),
        interpSU (transSU σ1 σ2) = subst (interpSU σ1) (interpSU σ2).
  Arguments SubstUnivLaws Sb {H}.

  Class SubstSULaws Sb `{SubstSU Sb T} {su : SubstUniv Sb} {sul : SubstUnivLaws Sb} :=
    substSU_trans : forall {Σ1 Σ2 Σ3} (σ1 : Sb Σ1 Σ2) (σ2 : Sb Σ2 Σ3) (t : T Σ1),
        substSU t (transSU σ1 σ2) = substSU (substSU t σ1) σ2.
  Arguments SubstSULaws Sb T {H su sul}.

  #[export] Instance substSubstSULaws `{Subst T, SubstLaws T} `{SubstUnivLaws Sb}
    : SubstSULaws Sb T.
  Proof.
    intros Σ1 Σ2 Σ3 σ1 σ2 t.
    unfold substSU, substSubstSU.
    now rewrite interpTransSU, subst_sub_comp.
  Qed.

  Record MeetResult `{SubstUniv Sb} Σ Σ1 Σ2 :=
    MkMeetResult {
        Σ12 : LCtx
      ; meetLeft : Sb Σ1 Σ12
      ; meetRight : Sb Σ2 Σ12
      ; meetUp : Sb Σ12 Σ
      }.

  Class SubstUnivMeet Sb `{SubstUniv Sb} :=
    meetSU : forall {Σ Σ1 Σ2} (σ1 : Sb Σ1 Σ) (σ2 : Sb Σ2 Σ), MeetResult Σ Σ1 Σ2
  .
  Arguments SubstUnivMeet Sb {H}.
  Class SubstUnivMeetLaws Sb `{SubstUnivMeet Sb} :=
    MkSubstUnivMeetLaws {
        meetLeftCorrect : forall {Σ Σ1 Σ2} (σ1 : Sb Σ1 Σ) (σ2 : Sb Σ2 Σ),
          transSU (meetLeft (meetSU σ1 σ2)) (meetUp (meetSU σ1 σ2)) = σ1
      ; meetRightCorrect : forall {Σ Σ1 Σ2} (σ1 : Sb Σ1 Σ) (σ2 : Sb Σ2 Σ),
          transSU (meetRight (meetSU σ1 σ2)) (meetUp (meetSU σ1 σ2)) = σ2
      }.
  Arguments SubstUnivMeetLaws Sb {H} {H0}.

  Class SubstUnivVar `{SubstUnivMeet Sb} :=
    suVar : forall {x Σ} (xIn : x ∈ Σ), Sb [ x ]%ctx  Σ.
  Arguments SubstUnivVar Sb {H} {H0}.

  Class SubstUnivVarUp `{SubstUnivVar Sb} :=
    upSU : forall {Σ1 Σ2 x}, Sb Σ1 Σ2 -> Sb (Σ1 ▻ x) (Σ2 ▻ x)
  .
  Arguments SubstUnivVarUp Sb {H H0 H1}.

  Class SubstUnivVarDown `{SubstUnivVar Sb} :=
    MkSubstUnivVarDown {
        wkVarSU : forall {Σ1 Σ2 x}, x ∈ Σ1 -> Sb Σ1 Σ2 -> x ∈ Σ2
      ; downSU : forall {Σ1 Σ2 x} (xIn : x ∈ Σ1) (σ : Sb Σ1 Σ2),
          let xIn' := wkVarSU xIn σ in Sb (Σ1 - x) (Σ2 - x)
      }.
  Arguments SubstUnivVarDown Sb {H H0 H1}.

  Class SubstUnivVarLaws `{SubstUnivVar Sb} :=
    suVarSound : forall `(xIn : x ∈ Σ), interpSU (suVar xIn) = [ term_var_in xIn ]%env.
  Arguments SubstUnivVarLaws Sb {H} {H0} {H1}.

  Class GenOccursCheck `{SubstUniv Sb} (T : LCtx -> Type) : Type :=
    gen_occurs_check : forall {Σ} (t : T Σ), { Σ' & (Sb Σ' Σ * T Σ')%type }.

  #[export] Instance GenOccursCheck_Const {Sb} {sSb : SubstUniv Sb} {A} : GenOccursCheck (Const A) :=
    fun Σ v => existT _ (initSU (SubstUniv := sSb), v).
  
  #[export] Instance gen_occurs_check_env `{SubstUnivMeet Sb}
    {I : Set} {T : LCtx -> I -> Set}
    {sT : forall i : I, Subst (fun Σ : LCtx => T Σ i)}
    {OCT : forall i, GenOccursCheck (fun Σ => T Σ i)} :
    forall {Γ : Ctx I}, GenOccursCheck (fun Σ => Env (T Σ) Γ) :=
    fix oc {Γ Σ} ts {struct ts} :=
      match ts with
      | env.nil         => existT [ctx] (initSU , [env])
      | env.snoc ts _ t =>
          let '(existT Σ1 (σ1 , ts')) := oc ts in
          let '(existT Σ2 (σ2 , t')) := gen_occurs_check t in
          let '(MkMeetResult _ _ _ _ Σ12 σ1' σ2' σ') := meetSU σ1 σ2 in
          existT Σ12 (σ' ,
                    (env.snoc (B := I) (substSU ts' σ1') _ (substSU t' σ2')))
      end.

  #[export] Instance gen_occurs_check_term `{SubstUnivVar Sb} :
    forall σ, GenOccursCheck (fun Σ => Term Σ σ) :=
    fix gen_occurs_check_term {τ Σ} (t : Term Σ τ) {struct t} :
      { Σ' & (Sb Σ' Σ * Term Σ' τ)%type } :=
      match t with
      | term_var_in xIn => existT _ (suVar xIn , term_var_in ctx.in_zero)
      | term_val σ v => existT [ctx] (initSU , term_val σ v)
      | term_binop op t1 t2 =>
          let '(existT Σ1 (σ1 , t1')) := gen_occurs_check_term t1 in
          let '(existT Σ2 (σ2 , t2')) := gen_occurs_check_term t2 in
          let '(MkMeetResult _ _ _ _ Σ12 σ1' σ2' σ') := meetSU σ1 σ2 in
          (existT Σ12 (σ' , term_binop op (substSU t1' σ1') (substSU t2' σ2')))
      | term_unop op t =>
          let '(existT Σ1 (σ1 , t')) := gen_occurs_check_term t in
          (existT Σ1 (σ1 , term_unop op t'))
      | term_tuple ts =>
        let '(existT Σ1 (σ1 , ts')) := gen_occurs_check_env (OCT := @gen_occurs_check_term) ts in
        (existT Σ1 (σ1 , term_tuple ts'))
      | term_union U K t0 =>
          let '(existT Σ1 (σ1 , ts')) := gen_occurs_check_term t0 in
          (existT Σ1 (σ1 , term_union U K ts'))
      | term_record R ts =>
        let OCTerm xt := @gen_occurs_check_term (@type recordf Ty xt) in
        let '(existT Σ1 (σ1 , ts')) := gen_occurs_check_env (OCT := OCTerm) ts in
        (existT Σ1 (σ1 , term_record R ts'))
      end.

  #[export] Instance gen_occurs_check_list `{SubstUnivMeet Sb} {T : LCtx -> Type} {sT : Subst T} `{ocT : GenOccursCheck Sb T} :
    GenOccursCheck (List T) :=
    fix oc {Σ} ls {struct ls} :=
      match ls with
      | nil => (existT [ctx] (initSU , nil))
      | (l :: ls)%list => let '(existT Σ1 (σ1 , l')) := gen_occurs_check l in
                          let '(existT Σ2 (σ2 , ls')) := oc ls in
                          let '(MkMeetResult _ _ _ _ Σ12 σ1' σ2' σ') := meetSU σ1 σ2 in
                          (existT Σ12 (σ' ,
                                    cons (substSU l' σ1') (substSU ls' σ2')))
      end.

  #[export] Instance gen_occurs_check_pair `{SubstUnivMeet Sb} `{GenOccursCheck Sb AT, GenOccursCheck Sb BT, Subst AT, Subst BT} :
    GenOccursCheck (Pair AT BT) :=
    fun _ '(a,b) =>
      let '(existT Σ1 (σ1 , a')) := gen_occurs_check a  in
      let '(existT Σ2 (σ2 , b')) := gen_occurs_check b  in
      let '(MkMeetResult _ _ _ _ Σ12 σ1' σ2' σ') := meetSU σ1 σ2 in
      (existT Σ12 (σ' , (substSU a' σ1', substSU b' σ2'))).

  #[export] Instance gen_occurs_check_option `{SubstUniv Sb} {AT} `{GenOccursCheck Sb AT} :
    GenOccursCheck (Option AT) :=
    fun _ ma =>
      match ma with
      | Some a => let '(existT Σ1 (σ1 , a')) := gen_occurs_check a in
                  (existT Σ1 (σ1 , Some a'))
      | None   => (existT [ctx] (initSU , None))
      end.

  #[export] Instance gen_occurscheck_ctx `{SubstUnivMeet Sb} {A} {sA : Subst A} {ocA : GenOccursCheck A} :
    GenOccursCheck (fun Σ => Ctx (A Σ)) :=
    fix oc {Σ} ys {struct ys} :=
      match ys with
      | ctx.nil       => (existT [ctx] (initSU , ctx.nil))
      | ctx.snoc ys y => let '(existT Σ1 (σ1 , ys')) := oc ys  in
                         let '(existT Σ2 (σ2 , y'))  := ocA _ y in
                         let '(MkMeetResult _ _ _ _ Σ12 σ1' σ2' σ') := meetSU σ1 σ2 in
                         (existT Σ12 (σ' , ctx.snoc (substSU ys' σ1') (substSU y' σ2')))
      end.

  Class GenOccursCheckLaws `{sSb : SubstUniv Sb}
    (T : LCtx -> Type)  {ocT : GenOccursCheck T} {sT : Subst T} : Type :=
    MkGenOccursCheckLaws {
       oc_sound : forall {Σ} (t : T Σ),
          let '(existT Σ' (σ , t')) := gen_occurs_check t in
          substSU t' σ = t
      }.
  Arguments GenOccursCheckLaws {Sb} {sSb} T {ocT} {sT}.

  (* Hm, I seem to need something more... *)
  (* Lemma oc_univ {Sb} {sSb : SubstUnivMeet Sb} *)
  (*   (T : LCtx -> Type) {sT : Subst T} {_ : GenOccursCheckLaws T} *)
  (*   {Σ1 Σ} {σ : Sb Σ1 Σ} {t : T Σ1} : *)
  (*   let '(existT Σ1' (σ1 , ts')) := (gen_occurs_check (subst t (interpSU σ))) in *)
  (*   exists σt, σ = transSU σt σ1. *)
  (* Proof. *)
  (*   generalize (oc_sound (subst t (interpSU σ))). *)
  (*   destruct (gen_occurs_check (subst t (interpSU σ))) as (Σ' & (σ' , t')). *)
  (*   destruct (meetSU σ' σ) as [Σ12 σ1' σ2' σ'' corrσ1' corrσ2']. *)
  (*   rewrite <- corrσ1', <-corrσ2'. *)
  (*   rewrite ?interpTransSU. *)
  (* Abort.  *)

  (* TODO: automate proofs... *)
  (* Ltac occurs_check_mixin := *)
  (*   match goal with *)
  (*   | H: ?P |- ?P => exact H *)
  (*   | |- ?x = ?x => refine eq_refl *)
  (*   | |- ?x = ?y => *)
  (*       let hx := head x in *)
  (*       let hy := head y in *)
  (*       is_constructor hx; is_constructor hy; *)
  (*       first [ subst; refine eq_refl (* | f_equal *) ] *)
  (*   | |- wlp _ (occurs_check ?xIn ?t) => *)
  (*       generalize (occurs_check_sound xIn t); *)
  (*       apply wlp_monotonic; intros ? -> *)
  (*   | |- wp _ (occurs_check ?xIn (subst ?t _)) => *)
  (*       generalize (occurs_check_shift xIn t); *)
  (*       apply wp_monotonic; intros ? := *)
  (*   | |- OccursCheckLaws _ => *)
  (*       constructor; unfold OccursCheckShiftPoint, OccursCheckSoundPoint; *)
  (*       let x := fresh in *)
  (*       intros ? ? ? x; induction x *)
  (*   end. *)

  (* Ltac occurs_check_derive := *)
  (*   repeat *)
  (*     (try progress cbn; *)
  (*      first *)
  (*        [ option.tactics.mixin *)
  (*        | occurs_check_mixin]); *)
  (*   try progress cbn; try easy. *)
  (* Local Ltac derive := occurs_check_derive. *)

  #[export, refine] Instance gen_occurs_check_laws_env `{SubstUnivVar Sb} {_ : SubstUnivLaws Sb} {_ : SubstUnivMeetLaws Sb}
    {I : Set} {T : LCtx -> I -> Set}
    {sT : forall i : I, Subst (fun Σ : LCtx => T Σ i)}
    {slT : forall i : I, SubstLaws (fun Σ : LCtx => T Σ i)}
    {OCT : forall i, GenOccursCheck (Sb := Sb) (fun Σ => T Σ i)}
    {OCTL : forall i, GenOccursCheckLaws (Sb := Sb) (fun Σ => T Σ i) } :
    forall {Γ : Ctx I}, GenOccursCheckLaws (Sb := Sb) (fun Σ => Env (T Σ) Γ) :=
    fun {Γ} => MkGenOccursCheckLaws _ _ _.
  Proof.
    induction t; first easy.
    cbn.
    change (gen_occurs_check_env t) with (gen_occurs_check (T := fun Σ => Env (T Σ) Γ) t).
    destruct (gen_occurs_check t) as (Σ1 & σ1 & t').
    generalize (oc_sound db).
    destruct (gen_occurs_check db) as (Σ2 & σ2 & db').
    intros Hdb.
    generalize (meetLeftCorrect σ1 σ2).
    generalize (meetRightCorrect σ1 σ2).
    destruct (meetSU σ1 σ2) as [Σ12 σ1' σ2' σ']; cbn -[subst].
    intros corrσ1 corrσ2.
    change (substSU (?x ► (?b ↦ ?xs))%env ?σ) with (substSU x σ ► (b ↦ substSU xs σ)).
    now rewrite <-?substSU_trans, corrσ1, corrσ2 , IHt, Hdb.
  Qed.

  #[export,refine] Instance gen_occurs_check_laws_term `{SubstUnivVarLaws Sb} {_ : SubstUnivLaws Sb} {_ : SubstUnivMeetLaws Sb} {τ} :
    GenOccursCheckLaws (fun Σ => Term Σ τ) :=
    MkGenOccursCheckLaws _ _ _.
  Proof.
    induction t; cbn.
    - now rewrite (suVarSound lIn).
    - easy.
    - revert IHt1 IHt2.
      change (gen_occurs_check_term ?t) with (gen_occurs_check (T := fun Σ => Term Σ _) t).
      destruct (gen_occurs_check t1) as (Σ1 & ς1 & t1').
      destruct (gen_occurs_check t2) as (Σ2 & ς2 & t2').
      generalize (meetLeftCorrect ς1 ς2).
      generalize (meetRightCorrect ς1 ς2).
      destruct (meetSU ς1 ς2) as [Σ12 ς1' ς2' ς]; cbn -[subst].
      intros  corrς1' corrς2'.
      intros Ht1 Ht2.
      change (substSU (term_binop ?op ?t1 ?t2) ?σ) with (term_binop op (substSU t1 σ) (substSU t2 σ)).
      now rewrite <-?substSU_trans, corrς1', corrς2', Ht1, Ht2.
    - revert IHt.
      change (gen_occurs_check_term ?t) with (gen_occurs_check (T := fun Σ => Term Σ _) t).
      destruct (gen_occurs_check t) as (Σ' & ς & t').
      now intros <-.
    - change (gen_occurs_check_env ?t) with (gen_occurs_check (T := fun Σ => Env (Term Σ) _) t).
      cut (let '(existT Σ' (σ, ts')) := gen_occurs_check ts in substSU (T := fun Σ => Env (Term Σ) _) ts' σ = ts).
      + destruct (gen_occurs_check ts) as (Σ1 & σ1 & t').
        now intros <-.
      + induction IH; first easy.
        cbn.
        change (gen_occurs_check_env ?t) with (gen_occurs_check (T := fun Σ => Env (Term Σ) _)t).
        destruct (gen_occurs_check E) as (Σ1 & σ1 & env').
        destruct (gen_occurs_check d) as (Σ2 & σ2 & d').
        generalize (meetLeftCorrect σ1 σ2).
        generalize (meetRightCorrect σ1 σ2).
        destruct (meetSU σ1 σ2) as [Σ12 σ1' σ2' σ']; cbn -[subst].
        intros  corrσ1 corrσ2.
        change (substSU ((?x ► (?b ↦ ?xs))%env) ?σ) with (substSU x σ ► (b ↦ substSU xs σ)).
        now rewrite <-?substSU_trans, corrσ1, corrσ2, IHIH, q.
    - change (gen_occurs_check_term ?t) with (gen_occurs_check (T := fun Σ => Term Σ _) t).
      destruct (gen_occurs_check t) as (Σ' & ς & t').
      change (substSU (term_union ?U ?K ?t) ?σ) with (term_union U K (substSU t σ)).
      now rewrite IHt.
    - change (gen_occurs_check_env ?t) with (gen_occurs_check (T := fun Σ => NamedEnv (Term Σ) _) t).
      cut (let '(existT Σ' (σ, ts')) := gen_occurs_check ts in substSU (T := fun Σ => NamedEnv (Term Σ) _) ts' σ = ts).
      + destruct (gen_occurs_check ts) as (Σ1 & σ1 & t').
        now intros <-.
      + induction IH; first easy.
        cbn.
        change (gen_occurs_check_env ?t) with (gen_occurs_check (T := fun Σ => Env (fun b => Term Σ _) _) t).
        destruct (gen_occurs_check E) as (Σ1 & σ1 & env').
        destruct (gen_occurs_check d) as (Σ2 & σ2 & d').
        generalize (meetLeftCorrect σ1 σ2).
        generalize (meetRightCorrect σ1 σ2).
        destruct (meetSU σ1 σ2) as [Σ12 σ1' σ2' σ']; cbn -[subst NamedEnv].
        intros  corrσ1 corrσ2.
        change (substSU ((?x ► (?b ↦ ?xs))%env) ?σ) with (substSU x σ ► (b ↦ substSU xs σ)).
        change (substSU env' σ1 = E) in IHIH.
        now rewrite <-?substSU_trans, corrσ1, corrσ2, q, IHIH.
  Qed.

  #[export,refine] Instance gen_occurs_check_laws_list `{SubstUnivMeet Sb} {_ : SubstUnivLaws Sb} {_ : SubstUnivMeetLaws Sb}
     `{SubstLaws T} {_ : GenOccursCheck T} {_ : GenOccursCheckLaws T} :
    GenOccursCheckLaws (List T) :=
    MkGenOccursCheckLaws _ _ _.
  Proof.
    induction t; first easy.
    cbn.
    generalize (oc_sound a).
    destruct (gen_occurs_check a) as (Σ1 & σ1 & a').
    intros <-.
    destruct (gen_occurs_check t) as (Σ2 & σ2 & t').
    generalize (meetLeftCorrect σ1 σ2).
    generalize (meetRightCorrect σ1 σ2).
    destruct (meetSU σ1 σ2) as [Σ12 σ1' σ2' σ']; cbn -[subst].
    intros  corrσ1 corrσ2.
    change (substSU (?x :: ?xs)%list ?σ) with (substSU x σ :: substSU xs σ)%list.
    now rewrite <-?substSU_trans, corrσ1, corrσ2, IHt.
  Qed.

  #[export] Instance gen_occurs_check_laws_sub `{SubstUnivVarLaws Sb} {_ : SubstUnivLaws Sb} {_ : SubstUnivMeetLaws Sb} {Σ} :
    GenOccursCheckLaws (Sub Σ) :=
    gen_occurs_check_laws_env.

  #[export,refine] Instance gen_occurs_check_laws_pair `{SubstUnivMeet Sb, SubstLaws AT, SubstLaws BT} {_ : SubstUnivLaws Sb} {_ : SubstUnivMeetLaws Sb}
    {_ : GenOccursCheck AT} {_ : GenOccursCheckLaws AT}
    {_ : GenOccursCheck BT} {_ : GenOccursCheckLaws BT} :
    GenOccursCheckLaws (Pair AT BT) :=
    MkGenOccursCheckLaws _ _ _.
  Proof.
    destruct t.
    cbn.
    generalize (oc_sound a).
    destruct (gen_occurs_check a) as (Σ1 & σ1 & a').
    generalize (oc_sound b).
    destruct (gen_occurs_check b) as (Σ2 & σ2 & b').
    generalize (meetLeftCorrect σ1 σ2).
    generalize (meetRightCorrect σ1 σ2).
    destruct (meetSU σ1 σ2) as [Σ12 σ1' σ2' σ']; cbn -[subst].
    intros corrσ1 corrσ2.
    change (substSU (?x , ?xs) ?σ) with (substSU x σ , substSU xs σ).
    rewrite <-?substSU_trans, corrσ1, corrσ2.
    now intros -> ->.
  Qed.

  #[export,refine] Instance gen_occurs_check_laws_option `{SubstUnivMeet Sb, SubstLaws AT} {_ : GenOccursCheck AT} {_ : GenOccursCheckLaws AT} :
    GenOccursCheckLaws (Option AT) :=
    MkGenOccursCheckLaws _ _ _.
  Proof.
    induction t; last easy.
    cbn.
    generalize (oc_sound a).
    destruct (gen_occurs_check a) as (Σ1 & σ1 & a').
    change (substSU (Some ?x) ?σ) with (Some (substSU x σ))%list.
    now intros ->.
  Qed.

  #[export] Instance gen_occurs_check_unit `{SubstUniv Sb} : GenOccursCheck Unit :=
    fun _ t => match t with tt => (existT [ctx] (initSU , tt)) end.

  #[export,refine] Instance gen_occurs_check_laws_unit `{SubstUniv Sb} :
    GenOccursCheckLaws Unit :=
    MkGenOccursCheckLaws _ _ _.
  Proof.
    now destruct t.
  Qed.

  #[export,refine] Instance gen_occurscheck_laws_ctx `{SubstUnivMeet Sb} {_ : SubstUnivLaws Sb} {_ : SubstUnivMeetLaws Sb}
    `{SubstLaws A} {_ :GenOccursCheck A} {_ :GenOccursCheckLaws A} :
    GenOccursCheckLaws (fun Σ => Ctx (A Σ)) :=
    MkGenOccursCheckLaws _ _ _.
  Proof.
    induction t; first easy.
    cbn.
    destruct (gen_occurs_check t) as (Σ1 & σ1 & a').
    generalize (oc_sound b).
    change (g _ ?t) with (gen_occurs_check t).
    destruct (gen_occurs_check b) as (Σ2 & σ2 & b').
    generalize (meetLeftCorrect σ1 σ2).
    generalize (meetRightCorrect σ1 σ2).
    destruct (meetSU σ1 σ2) as [Σ12 σ1' σ2' σ']; cbn -[subst].
    intros corrσ1 corrσ2.
    change (substSU (?x ▻ ?xs) ?σ) with (substSU x σ ▻ substSU xs σ).
    rewrite <-?substSU_trans, corrσ1, corrσ2, IHt.
    now intros ->.
  Qed.

  Section Weakenings.
    Inductive WeakensTo : LCtx -> LCtx -> Set :=
    | WkNil : WeakensTo [ctx] [ctx]
    | WkSkipVar : forall {Σ1 Σ2} x, WeakensTo Σ1 Σ2 -> WeakensTo Σ1 (Σ2 ▻ x)
    | WkKeepVar : forall {Σ1 Σ2} x, WeakensTo Σ1 Σ2 -> WeakensTo (Σ1 ▻ x) (Σ2 ▻ x)
    .

    Fixpoint interpWk {Σ1 Σ2} (wk : WeakensTo Σ1 Σ2) : Sub Σ1 Σ2 :=
      match wk with
      | WkNil => [env]
      | WkSkipVar x wk => subst (interpWk wk) sub_wk1
      | WkKeepVar x wk => sub_up1 (interpWk wk)
      end.

    Equations transWk {Σ1 Σ2 Σ3} (wk12 : WeakensTo Σ1 Σ2) (wk23 : WeakensTo Σ2 Σ3) : WeakensTo Σ1 Σ3 :=
    | wk1 | WkSkipVar _ wk2 => WkSkipVar _ (transWk wk1 wk2)
    | WkNil | wk2 => wk2
    | WkSkipVar x wk1 | WkKeepVar _ wk2 => WkSkipVar _ (transWk wk1 wk2)
    | WkKeepVar x wk1 | WkKeepVar _ wk2 => WkKeepVar _ (transWk wk1 wk2)
    .

    Lemma interpTransWk {Σ1 Σ2 Σ3} (wk12 : WeakensTo Σ1 Σ2) (wk23 : WeakensTo Σ2 Σ3) :
      interpWk (transWk wk12 wk23) = subst (interpWk wk12) (interpWk wk23).
    Proof.
      eapply (transWk_elim (fun Σ1 Σ2 Σ3 wk12 wk23 wk13 => interpWk wk13 = subst (Subst := SubstEnv) (interpWk wk12) (interpWk wk23)));
        cbn -[subst].
      - now intros.
      - intros * ->.
        apply sub_comp_assoc.
      - intros * ->.
        rewrite !(sub_comp_assoc (interpWk wk1)).
        now rewrite sub_comp_wk1_comm.
      - intros * ->.
        apply sub_up1_comp.
    Defined.

    Fixpoint wkNilInit {Σ} : WeakensTo [ctx] Σ :=
      match Σ with
      | [ctx] => WkNil
      | Σ ▻ x => WkSkipVar x wkNilInit
      end.

    Fixpoint wkRefl {Σ} : WeakensTo Σ Σ :=
      match Σ with
      | [ctx] => WkNil
      | Σ ▻ x => WkKeepVar x wkRefl
      end.

    Inductive WeakenZeroView Σ2 b : forall Σ1, WeakensTo Σ1 (Σ2 ▻ b) -> Type :=
    | VarUnused : forall Σ1 (wk : WeakensTo Σ1 Σ2), WeakenZeroView (WkSkipVar b wk)
    | VarUsed : forall Σ1 (wk : WeakensTo Σ1 Σ2), WeakenZeroView (WkKeepVar b wk)
    .

    Equations weakenZeroView {Σ1 Σ2 b} (wk : WeakensTo Σ1 (Σ2 ▻ b)) : WeakenZeroView wk :=
    | WkSkipVar _ wk => VarUnused b wk
    | WkKeepVar _ wk => VarUsed b wk
    .

    Fixpoint wkRemove (Σ : LCtx) b (bIn : b ∈ Σ) : WeakensTo (Σ - b) Σ :=
      ctx.In_case (fun b Σ bIn => WeakensTo (Σ - b) Σ)
                  (fun b Σ => WkSkipVar _ wkRefl)
                  (fun b' Σ b bIn => WkKeepVar _ (wkRemove bIn))
                  bIn.

    Fixpoint wkSingleton {Σ : LCtx} {b} (bIn : b ∈ Σ) : WeakensTo [ b ]%ctx Σ :=
      ctx.In_case (fun b Σ bIn => WeakensTo [ b ]%ctx Σ)
                  (fun b Σ => WkKeepVar _ wkNilInit)
                  (fun b' Σ b bIn => WkSkipVar _ (wkSingleton bIn))
                  bIn.

    Equations wkVarZeroIn {Σ Σ' : LCtx} {b} (σ : WeakensTo (Σ' ▻ b)%ctx Σ) : b ∈ Σ :=
    | WkKeepVar _ _ => ctx.in_zero
    | WkSkipVar _ wk => ctx.in_succ (wkVarZeroIn wk)
    .

    Fixpoint weakenIn {Σ1 Σ2 : LCtx} (σ : WeakensTo Σ1 Σ2) : forall {b} (bIn : b ∈ Σ1), b ∈ Σ2 :=
      match σ with
      | WkNil => fun b (bIn : b ∈ [ctx]) => match ctx.view bIn with end
      | WkSkipVar _ σ' => fun b bIn => ctx.in_succ (weakenIn σ' bIn)
      | WkKeepVar _ σ' => fun b bIn => match ctx.view bIn with
                                     | ctx.isZero => ctx.in_zero
                                     | ctx.isSucc bIn' => ctx.in_succ (weakenIn σ' bIn')
                                     end
      end.

    Lemma weakenRemovePres {Σ1 Σ2} (wk : WeakensTo Σ1 Σ2) :
      forall {b} (bIn : b ∈ Σ1),
        let bIn' := weakenIn wk bIn in WeakensTo (Σ1 - b) (Σ2 - b).
    Proof.
      induction wk; intros b bIn.
      - destruct (ctx.view bIn).
      - apply WkSkipVar, IHwk.
      - destruct (ctx.view bIn); first easy.
        apply WkKeepVar, IHwk.
    Defined.

    Inductive WeakenRemoveView {Σ b} : forall {Σ1} (bIn : b ∈ Σ), WeakensTo Σ1 (Σ - b) -> Set :=
    | MkWeakenRemoveView : forall Σ1' (bIn' : b ∈ Σ1') (σ1' : WeakensTo Σ1' Σ), WeakenRemoveView (weakenIn σ1' bIn') (weakenRemovePres σ1' bIn').

    Definition weakenRemoveView : forall {b Σ} (bIn : b ∈ Σ) Σ1 (σ : WeakensTo Σ1 (Σ - b)), WeakenRemoveView bIn σ :=
        ctx.In_rect (fun b Σ bIn => forall Σ1 σ, WeakenRemoveView bIn σ)
                  (fun b Σ Σ1 σ => MkWeakenRemoveView ctx.in_zero (WkKeepVar _ σ))
                  (fun b Σ b' bIn IHbIn Σ1 σ =>
                     match weakenZeroView σ with
                     | VarUsed _ σ' =>
                         match IHbIn _ σ'
                               in WeakenRemoveView bIn σ'
                               return WeakenRemoveView (ctx.in_succ bIn) _ with
                         | (MkWeakenRemoveView bIn' σ1') =>
                             MkWeakenRemoveView (ctx.in_succ bIn') (WkKeepVar _ σ1')
                         end
                     | VarUnused _ σ' =>
                         match IHbIn _ σ'
                               in WeakenRemoveView bIn σ'
                               return WeakenRemoveView (ctx.in_succ bIn) _ with
                         | MkWeakenRemoveView bIn' σ1' =>
                             MkWeakenRemoveView bIn' (WkSkipVar _ σ1')
                         end
                     end
                  ).

    #[export] Instance substUniv_weaken : SubstUniv WeakensTo.
    Proof.
      econstructor.
      - intros. exact wkNilInit.
      - intros. eapply transWk; eassumption.
      - intros; now eapply interpWk.
    Defined.

    Definition extendMeetSkipSkip {Σ1 Σ2 Σ3 x} (meet : MeetResult Σ3 Σ1 Σ2) :
      MeetResult (Σ3 ▻ x) Σ1 Σ2 :=
      match meet with
        MkMeetResult _ _ _ _ Σ12 σ1' σ2' σ' => MkMeetResult _ _ _ _ Σ12 σ1' σ2' (WkSkipVar x σ')
      end.
    Definition extendMeetSkipKeep {Σ1 Σ2 Σ3 x} (meet : MeetResult Σ3 Σ1 Σ2) :
      MeetResult (Σ3 ▻ x) Σ1 (Σ2 ▻ x) :=
      match meet with
        MkMeetResult _ _ _ _ Σ12 σ1' σ2' σ' => MkMeetResult _ _ _ _ _ (WkSkipVar x σ1') (WkKeepVar _ σ2') (WkKeepVar x σ')
      end.
    Definition extendMeetKeepSkip {Σ1 Σ2 Σ3 x} (meet : MeetResult Σ3 Σ1 Σ2) :
      MeetResult (Σ3 ▻ x) (Σ1 ▻ x) Σ2 :=
      match meet with
        MkMeetResult _ _ _ _ Σ12 σ1' σ2' σ' => MkMeetResult _ _ _ _ _ (WkKeepVar x σ1') (WkSkipVar _ σ2') (WkKeepVar x σ')
      end.
    Definition extendMeetKeepKeep {Σ1 Σ2 Σ3 x} (meet : MeetResult Σ3 Σ1 Σ2) :
      MeetResult (Σ3 ▻ x) (Σ1 ▻ x) (Σ2 ▻ x) :=
      match meet with
        MkMeetResult _ _ _ _ Σ12 σ1' σ2' σ'  => MkMeetResult _ _ _ _ _ (WkKeepVar x σ1') (WkKeepVar _ σ2') (WkKeepVar x σ')
      end.
    Equations meetWk {Σ1 Σ2 Σ3} (wk13 : WeakensTo Σ1 Σ3) (wk23 : WeakensTo Σ2 Σ3) :
      MeetResult Σ3 Σ1 Σ2 :=
    | WkNil | WkNil => MkMeetResult _ _ _ _ _ WkNil WkNil WkNil
    | WkSkipVar x wk1 | WkSkipVar _ wk2 => extendMeetSkipSkip (meetWk wk1 wk2)
    | WkSkipVar x wk1 | WkKeepVar _ wk2 => extendMeetSkipKeep (meetWk wk1 wk2)
    | WkKeepVar x wk1 | WkSkipVar _ wk2 => extendMeetKeepSkip (meetWk wk1 wk2)
    | WkKeepVar x wk1 | WkKeepVar _ wk2 => extendMeetKeepKeep (meetWk wk1 wk2)
    .

    #[export] Instance substUnivMeet_weaken : SubstUnivMeet WeakensTo :=
      fun _ _ _ => meetWk.
    #[export] Instance substUnivMeetLaws_weaken : SubstUnivMeetLaws WeakensTo.
    Proof.
      constructor; intros.
      - apply (meetWk_elim (fun _ _ _ wk1 wk2 res => transSU (meetLeft res) (meetUp res) = wk1));
        cbn; first reflexivity; intros;
        destruct (meetWk wk1 wk2) as [Σ12 σ1' σ2' σ']; cbn in *;
          rewrite ?transWk_equation_2, ?transWk_equation_3, ?transWk_equation_4;
          now f_equal.
      - apply (meetWk_elim (fun _ _ _ wk1 wk2 res => transSU (meetRight res) (meetUp res) = wk2));
        cbn; first reflexivity; intros;
        destruct (meetWk wk1 wk2) as [Σ12 σ1' σ2' σ']; cbn in *;
          rewrite ?transWk_equation_2, ?transWk_equation_3, ?transWk_equation_4;
          now f_equal.
    Qed.

    Definition wkVar : forall {x Σ}, x ∈ Σ -> WeakensTo [ x ]%ctx Σ :=
      ctx.In_rect (fun x Σ xIn => WeakensTo [ x ]%ctx Σ)
                  (fun x Σ => WkKeepVar x wkNilInit)
                  (fun x Σ y xIn wk => WkSkipVar y wk).

    Lemma interpWk_wkVar : forall {x Σ} {xIn : x ∈ Σ},
      interpWk (wkVar xIn) = [ term_var_in xIn ]%env.
    Proof.
      eapply ctx.In_ind.
      - intros.
        refine (f_equal (fun x => x.[b ↦ _]) _).
        match goal with |- ?env = [env] => now destruct (env.view env) end.
      - intros.
        change (interpWk (wkVar (ctx.in_succ bIn))) with
                 (subst (interpWk (wkVar bIn)) (sub_wk1 (b := b'))).
        rewrite H.
        cbn.
        now rewrite lookup_sub_wk1.
    Qed.

    #[export] Instance substUnivVar_weaken : SubstUnivVar WeakensTo :=
      (fun x Σ xIn => wkVar xIn).
    #[export] Instance substUnivVarUp_weaken : SubstUnivVarUp WeakensTo.
    Proof.
      intros Σ1 Σ2 x σ; now eapply WkKeepVar.
    Defined.
    #[export] Instance substUnivVarDown_weaken : SubstUnivVarDown WeakensTo.
    Proof.
      refine (MkSubstUnivVarDown _ (fun _ _ _ xIn σ => weakenIn σ xIn) _).
      intros; eapply weakenRemovePres.
    Defined.

    #[export] Instance substUnivVarLaws_weaken : SubstUnivVarLaws WeakensTo :=
      (fun _ _ xIn => interpWk_wkVar).

    Fixpoint restrictEnv {D} {Σ1 Σ2 : LCtx} (wk : WeakensTo Σ1 Σ2) :
      Env D Σ2 -> Env D Σ1.
    Proof.
      induction wk; first easy.
      intros e. eapply IHwk, env.tail. now eassumption.
      intros e. destruct (env.view e) as [e v].
      apply env.snoc; last easy.
      now eapply IHwk.
    Qed.

  End Weakenings.

End GenOccursCheckOn.
