From iris.prelude Require Export prelude.
From iris.bi Require Export bi.
From iris.proofmode Require Import base environments classes string_ident ltac_tactics coq_tactics reduction intro_patterns ltac_tactics.
From iris.prelude Require Import options.
Import bi.

Definition pre_envs_entails_cocontexts_def {PROP : bi} (Γp Γs : env PROP) (Qp Qs : env PROP) :=
  of_envs' Γp Γs ⊢ of_envs' Qp Qs.
Definition pre_envs_entails_cocontexts_aux : seal (@pre_envs_entails_cocontexts_def). Proof. by eexists. Qed.
Definition pre_envs_entails_cocontexts := pre_envs_entails_cocontexts_aux.(unseal).
Definition pre_envs_entails_cocontexts_eq : @pre_envs_entails_cocontexts = @pre_envs_entails_cocontexts_def :=
  pre_envs_entails_cocontexts_aux.(seal_eq).

Definition envs_entails_cocontexts {PROP : bi} (Δ : envs PROP) (Q : envs PROP) : Prop :=
  pre_envs_entails_cocontexts  PROP (env_intuitionistic Δ) (env_spatial Δ) (env_intuitionistic Q) (env_spatial Q).
Definition envs_entails_cocontexts_eq :
  @envs_entails_cocontexts = λ PROP (Δ : envs PROP) Q, (of_envs Δ ⊢ of_envs Q).
Proof. by rewrite /envs_entails_cocontexts pre_envs_entails_cocontexts_eq. Qed.
Global Arguments envs_entails_cocontexts {PROP} Δ Q%I.
Global Instance: Params (@envs_entails_cocontexts) 1 := {}.


Declare Scope cocontexts_scope.
Delimit Scope cocontexts_scope with env.
Global Arguments Envs _ _%cocontexts_scope _%cocontexts_scope _.
Global Arguments Enil {_}.
Global Arguments Esnoc {_} _%cocontexts_scope _%string _%I.

Notation "" := Enil (only printing) : cocontexts_scope.
Notation "Γ H : P" := (Esnoc Γ (INamed H) P%I)
  (at level 1, P at level 200,
   left associativity, format "Γ H  :  '[' P ']' '//'", only printing) : cocontexts_scope.
Notation "Γ '_' : P" := (Esnoc Γ (IAnon _) P%I)
  (at level 1, P at level 200,
   left associativity, format "Γ '_'  :  '[' P ']' '//'", only printing) : cocontexts_scope.

Notation "Γ '--------------------------------------' □ Δ '--------------------------------------' ∗ Qi '--------------------------------------' □ Qp " :=
  (envs_entails_cocontexts (Envs Γ Δ _) (Envs Qi Qp _)%I)
  (at level 1, Qi at level 200, Qp at level 200, left associativity,
  format "'[' Γ '--------------------------------------' □ '//' Δ '--------------------------------------' ∗ '//' Qi '--------------------------------------' □ '//' Qp ']'", only printing) :
  stdpp_scope.
Notation "Δ '--------------------------------------' ∗ Qp" :=
  (envs_entails_cocontexts (Envs Enil Δ _) (Envs Enil Qp _)%I)
  (at level 1, Qp at level 200, left associativity,
  format "'[' Δ '--------------------------------------' ∗ '//' Qp ']'", only printing) : stdpp_scope.
Notation "Γ '--------------------------------------' □ Qp" :=
  (envs_entails_cocontexts (Envs Γ Enil _) (Envs Enil Qp _)%I)
  (at level 1, Qp at level 200, left associativity,
  format "'[' Γ '--------------------------------------' □ '//' Qp ']'", only printing)  : stdpp_scope.
Notation "'--------------------------------------' ∗ Qp" :=
  (envs_entails_cocontexts (Envs Enil Enil _) (Envs Enil Qp _)%I)
  (at level 1, Qp at level 200, format "'[' '--------------------------------------' ∗ '//' Qp ']'", only printing) : stdpp_scope.

Section tactics.
Context {PROP : bi}.

Implicit Types Γ : env PROP.
Implicit Types Δ : envs PROP.
Implicit Types A : envs PROP.
Implicit Types P : PROP.

Lemma envs_simple_replace_sound_2 Δ Δ' i p P Γ :
  envs_lookup i Δ = Some (p,P) → envs_simple_replace i p Γ Δ = Some Δ' →
  (bi_intuitionistically_if p P -∗ (if p then □ [∧] Γ else [∗] Γ)) ⊢ (of_envs Δ' -∗ of_envs Δ).
Proof. (* intros. by rewrite envs_lookup_sound// envs_simple_replace_sound'//. *)
Admitted.

Lemma tac_and_codestruct Δ i p j1 j2 P P1 P2 Q :
  envs_lookup i Q = Some (p, P) →
  (if p then IntoAnd true P P2 P1 else IntoSep P P2 P1) →
  match envs_simple_replace i p (Esnoc (Esnoc Enil j2 P1) j1 P2) Q with
  | None => False
  | Some Q' => envs_entails_cocontexts Δ Q'
  end →
  envs_entails_cocontexts Δ Q.
Proof.
  destruct (envs_simple_replace _ _ _ _) as [Δ'|] eqn:Hrep; last done.
  rewrite envs_entails_cocontexts_eq. intros.
  rewrite H1; clear H1 Δ.
  rewrite (wand_entails (of_envs Δ') (of_envs Q)); first done.
  rewrite <-(envs_simple_replace_sound_2 _ _ _ _ _ _ H Hrep).
  destruct p.
  - cbn.
    rewrite and_True.
    rewrite <-(into_and true P P2 P1).
    now apply entails_wand.
  - cbn.
    rewrite sep_emp.
    rewrite <-(into_sep P P2 P1).
    now apply entails_wand.
Qed.

Lemma tac_corename Δ i j p P Q :
  envs_lookup i Q = Some (p,P) →
  match envs_simple_replace i p (Esnoc Enil j P) Q with
  | None => False
  | Some Q' => envs_entails_cocontexts Δ Q'
  end →
  envs_entails_cocontexts Δ Q.
Proof.
  destruct (envs_simple_replace _ _ _ _) as [Q' |] eqn:Hrep; last done.
  rewrite envs_entails_cocontexts_eq=> Hlkp HΔQp.
  rewrite HΔQp; clear HΔQp.
  assert (□?p P ⊢ if p then □ [∧] Esnoc Enil j P else [∗] Esnoc Enil j P)%I.
  { destruct p; cbn.
    - now rewrite and_True.
    - now rewrite sep_emp.
  }
  apply entails_wand in H.
  pose proof (envs_simple_replace_sound_2 _ _ _ _ _ _ Hlkp Hrep).
  rewrite <-H in H0.
  now apply wand_entails.
Qed.

Lemma tac_start_cocontexts P (Γ : envs PROP) : envs_entails_cocontexts Γ (Envs Enil (Esnoc Enil "Goal" P) 1%positive) -> envs_entails Γ P.
Proof.
  rewrite envs_entails_eq !of_envs_eq /=.
  rewrite envs_entails_cocontexts_eq !of_envs_eq /=.
  rewrite intuitionistically_True_emp.
  rewrite left_id right_id.
  now rewrite (and_elim_r (bi_pure _) P).
Qed.

Definition denote_env_helper Δ :=
  (match env_intuitionistic Δ, env_spatial Δ with
   | Enil, Γs => env_to_prop Γs
   | Γp, Enil => □ env_to_prop_and Γp
   | Γp, Γs => □ env_to_prop_and Γp ∗ env_to_prop Γs
  end)%I.

Lemma denote_env_sound Δ : denote_env_helper Δ ⊣⊢ of_envs Δ.
Proof.
  destruct Δ as [Δi Δs]; unfold denote_env_helper; cbn.
  rewrite !of_envs_eq.
Admitted.

Lemma tac_stop_cocontexts Δh Δg :
  (denote_env_helper Δh ⊢ denote_env_helper Δg) →
  envs_entails_cocontexts Δh Δg.
Proof.
  now rewrite envs_entails_cocontexts_eq !denote_env_sound.
Qed.

Lemma tac_frame_hyp Δh Δc i j p P :
  envs_lookup i Δh = Some (p, P) →
  envs_lookup j Δc = Some (p, P) →
  envs_entails_cocontexts (envs_delete false i p Δh) (envs_delete false j p Δc) →
  envs_entails_cocontexts Δh Δc.
Proof.
(*   rewrite envs_entails_cocontexts_eq. intros ? Hframe HQ. *)
(*   rewrite (envs_lookup_sound' _ false) //. by rewrite -Hframe HQ. *)
(* Qed. *)
Admitted.

Lemma tac_frame_hyp_in Δh Δc i j Δc' p R P Q :
  envs_lookup i Δh = Some (p, P) →
  envs_lookup j Δc = Some (p, R) →
  Frame p R P Q →
  (envs_simple_replace i p (Esnoc Enil j Q) Δc) = Some Δc' ->
  envs_entails_cocontexts (envs_delete false i p Δh) Δc' →
  envs_entails_cocontexts Δh Δc.
Proof.
(*   rewrite envs_entails_cocontexts_eq. intros ? Hframe HQ. *)
(*   rewrite (envs_lookup_sound' _ false) //. by rewrite -Hframe HQ. *)
(* Qed. *)
Admitted.

Class FromPureEnv {PROP : bi} (a : bool) (P : env PROP) (φ : Prop) :=
  from_pure_env : <affine>?a ⌜φ⌝ ⊢ [∗] P.
Global Arguments FromPureEnv {_} _ _%I _%type_scope : simpl never.
Global Arguments from_pure_env {_} _ _%I _%type_scope {_}.
Global Hint Mode FromPureEnv + - ! - : typeclass_instances.

Global Instance from_pure_env_nil :
  FromPureEnv false (Enil : env PROP) True.
Admitted.

Global Instance from_pure_env_snoc {a} {Γ : env PROP} {Γt P Pt i} :
  forall `{! FromPureEnv a Γ Γt}
  `{! FromPure a P Pt},
    FromPureEnv a (Esnoc Γ i P) (Γt /\ Pt).
Admitted.

(** * Pure *)
Lemma tac_pure_intro Δh (Δc : env PROP) φ c' :
  FromPureEnv false Δc φ →
  (* (if a then AffineEnv (env_spatial Δc) else TCTrue) → *)
  φ →
  envs_entails_cocontexts Δh (Envs Enil Δc c').
(* Proof. *)
(*   intros ???. rewrite envs_entails_eq -(from_pure a Q). destruct a; simpl. *)
(*   - by rewrite (affine (of_envs Δ)) pure_True // affinely_True_emp affinely_emp. *)
(*   - by apply pure_intro. *)
(* Qed. *)
Admitted.

End tactics.

Tactic Notation "iAndCodestructCohyp" constr(H) "as" constr(H1) constr(H2) :=
  eapply tac_and_codestruct with H _ H1 H2 _ _ _;
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iCoDestructCoHypAnd:" H "not found"
    |pm_reduce; iSolveTC ||
     let P :=
       lazymatch goal with
       | |- IntoSep ?P _ _ => P
       | |- IntoAnd _ ?P _ _ => P
       end in
     fail "iAndDestruct: cannot destruct" P
    |pm_reduce;
     lazymatch goal with
       | |- False =>
         let H1 := pretty_ident H1 in
         let H2 := pretty_ident H2 in
         fail "iAndDestruct:" H1 "or" H2 "not fresh"
       | _ => idtac (* subgoal *)
     end].

(** * Context manipulation *)
Tactic Notation "iCoRename" constr(H1) "into" constr(H2) :=
  eapply tac_corename with H1 H2 _ _; (* (i:=H1) (j:=H2) *)
    [pm_reflexivity ||
     let H1 := pretty_ident H1 in
     fail "iCoRename:" H1 "not found"
    |pm_reduce;
     lazymatch goal with
       | |- False =>
         let H2 := pretty_ident H2 in
         fail "iRename:" H2 "not fresh"
       | _ => idtac (* subgoal *)
     end].

(** * Start a proof *)
Tactic Notation "iStartProof" :=
  lazymatch goal with
  | |- envs_entails _ _ => eapply tac_start_cocontexts
  | |- envs_entails_cocontexts _ _ => idtac
  | |- ?φ => notypeclasses refine (as_emp_valid_2 φ _ _);
           eapply tac_start_cocontexts;
               [iSolveTC || fail "iStartProof: not a BI assertion"
               |notypeclasses refine (tac_start _ _)]
  end.

Tactic Notation "iStopProof" :=
  lazymatch goal with
  | |- envs_entails _ _ => apply tac_stop; pm_reduce
  | |- envs_entails_cocontexts _ _ => apply tac_stop_cocontexts; pm_reduce
  | |- _ => fail "iStopProof: proofmode not started"
  end.

Ltac iFrameHyp Hh Hc :=
  iStartProof;
  eapply tac_frame_hyp with Hh Hc _ _;
    [pm_reflexivity ||
     let H := pretty_ident Hh in
     fail "iFrame:" Hh "not found"
    |pm_reflexivity ||
     let H := pretty_ident Hh in
     fail "iFrame:" Hh "not found"
    |pm_reduce; iFrameFinish].

Ltac iFrameHypIn Hh Hc :=
  iStartProof;
  eapply tac_frame_hyp_in with Hh Hc _ _ _ _ _;
    [pm_reflexivity ||
     let H := pretty_ident Hh in
     fail "iFrame:" Hh "not found"
    |pm_reflexivity ||
     let H := pretty_ident Hh in
     fail "iFrame:" Hh "not found"
    |iSolveTC ||
     let R := match goal with |- Frame _ ?R _ _ => R end in
     fail "iFrame: cannot frame" R
    |pm_reduce; iFrameFinish].

Ltac iFresh :=
  (* We make use of an Ltac hack to allow the [iFresh] tactic to both have a
  side-effect (i.e. to bump the counter) and to return a value (the fresh name).
  We do this by wrapped the side-effect under a [match] in a let-binding. See
  https://stackoverflow.com/a/46178884 *)
  let start :=
    lazymatch goal with
    | _ => iStartProof
    end in
  let c :=
    lazymatch goal with
    | |- envs_entails (Envs _ _ ?c) _ => c
    | |- envs_entails_cocontexts (Envs _ _ ?c) _ => c
    end in
  let inc :=
    lazymatch goal with
    | |- envs_entails (Envs ?Δp ?Δs _) ?Q =>
      let c' := eval vm_compute in (Pos.succ c) in
      change_no_check (envs_entails (Envs Δp Δs c') Q)
    | |- envs_entails_cocontexts (Envs ?Δp ?Δs _) ?Q =>
      let c' := eval vm_compute in (Pos.succ c) in
      change_no_check (envs_entails_cocontexts (Envs Δp Δs c') Q)
    end in
  constr:(IAnon c).

(* stolen from iris.proofmode.coq_tactics *)
Local Ltac ident_for_pat pat :=
  lazymatch pat with
  | IIdent ?x => x
  | _ => let x := iFresh in x
  end.

Local Ltac ident_for_pat_default pat default :=
  lazymatch pat with
  | IIdent ?x => x
  | _ =>
    lazymatch default with
    | IAnon _ => default
    | _ => let x := iFresh in x
    end
  end.

Tactic Notation "iPureIntro" :=
  iStartProof;
  eapply tac_pure_intro;
    [iSolveTC ||
     let P := match goal with |- FromPureEnv _ ?P _ => P end in
     match goal with |- ?H => idtac H end;
     fail "iPureIntro:" P "not pure"
    (* |pm_reduce; iSolveTC || *)
    (*  fail "iPureIntro: spatial context contains non-affine hypotheses" *)
    |].


(** [pat0] is the unparsed pattern, and is only used in error messages *)
Ltac iCodestructCohypGo Hz pat0 pat :=
  lazymatch pat with
  (* | IFresh => *)
  (*    lazymatch Hz with *)
  (*    | IAnon _ => idtac *)
  (*    | INamed ?Hz => let Hz' := iFresh in iRename Hz into Hz' *)
  (*    end *)
  (* | IDrop => iClearHyp Hz *)
  (* | IFrame => iFrameHyp Hz *)
  | IIdent Hz => idtac
  | IIdent ?y => iRename Hz into y
  (* | IList [[]] => iExFalso; iExact Hz *)

  (* conjunctive patterns like [H1 H2] *)
  (* | IList [[?pat1; IDrop]] => *)
  (*    let x := ident_for_pat_default pat1 Hz in *)
  (*    iAndDestructChoice Hz as Left x; *)
  (*    iDestructHypGo x pat0 pat1 *)
  (* | IList [[IDrop; ?pat2]] => *)
  (*    let x := ident_for_pat_default pat2 Hz in *)
  (*    iAndDestructChoice Hz as Right x; *)
  (*    iDestructHypGo x pat0 pat2 *)
  (* [% ...] is always interpreted as an existential; there are [IntoExist]
  instances in place to handle conjunctions with a pure left-hand side this way
  as well. *)
  (* | IList [[IPure IGallinaAnon; ?pat2]] => *)
  (*    let x := ident_for_pat_default pat2 Hz in *)
  (*    iExistDestruct Hz as ? x; iDestructHypGo x pat0 pat2 *)
  (* | IList [[IPure (IGallinaNamed ?s); ?pat2]] => *)
  (*    let x := fresh in *)
  (*    let y := ident_for_pat_default pat2 Hz in *)
  (*    iExistDestruct Hz as x y; *)
  (*    rename_by_string x s; *)
  (*    iDestructHypGo y pat0 pat2 *)
  | IList [[?pat1; ?pat2]] =>
     (* We have to take care of not using the same name for the two hypotheses: *)
  (*       [ident_for_pat_default] will thus only reuse [Hz] (which could in principle *)
  (*       clash with a name from [pat2]) if it is an anonymous name. *)
     let x1 := ident_for_pat_default pat1 Hz in
     let x2 := ident_for_pat pat2 in
     iAndCodestructCohyp Hz as x1 x2;
     iCodestructCohypGo x1 pat0 pat1;
     iCodestructCohypGo x2 pat0 pat2
  (* | IList [_ :: _ :: _] => fail "iDestruct:" pat0 "has too many conjuncts" *)
  (* | IList [[_]] => fail "iDestruct:" pat0 "has just a single conjunct" *)

  (* disjunctive patterns like [H1|H2] *)
  (* | IList [[?pat1];[?pat2]] => *)
  (*    let x1 := ident_for_pat_default pat1 Hz in *)
  (*    let x2 := ident_for_pat_default pat2 Hz in *)
  (*    iOrDestruct Hz as x1 x2; *)
  (*    [iDestructHypGo x1 pat0 pat1|iDestructHypGo x2 pat0 pat2] *)
  (* this matches a list of three or more disjunctions [H1|H2|H3] *)
  (* | IList (_ :: _ :: _ :: _) => fail "iDestruct:" pat0 "has too many disjuncts" *)
  (* the above patterns don't match [H1 H2|H3] *)
  (* | IList [_;_] => fail "iDestruct: in" pat0 "a disjunct has multiple patterns" *)

  (* | IPure IGallinaAnon => iPure Hz as ? *)
  (* | IPure (IGallinaNamed ?s) => *)
  (*    let x := fresh in *)
  (*    iPure Hz as x; *)
  (*    rename_by_string x s *)
  (* | IRewrite Right => iPure Hz as -> *)
  (* | IRewrite Left => iPure Hz as <- *)
  (* | IIntuitionistic ?pat => *)
  (*   let x := ident_for_pat_default pat Hz in *)
  (*   iIntuitionistic Hz as x; iDestructHypGo x pat0 pat *)
  (* | ISpatial ?pat => *)
  (*   let x := ident_for_pat_default pat Hz in *)
  (*   iSpatial Hz as x; iDestructHypGo x pat0 pat *)
  (* | IModalElim ?pat => *)
  (*   let x := ident_for_pat_default pat Hz in *)
  (*   iModCore Hz as x; iDestructHypGo x pat0 pat *)
  | _ => fail "iDestruct:" pat0 "is not supported due to" pat
  end.

Local Ltac iCodestructCohypFindPat Hgo pat found pats :=
  lazymatch pats with
  | [] =>
    lazymatch found with
    | true => pm_prettify (* post-tactic prettification *)
    | false => fail "iDestruct:" pat "should contain exactly one proper introduction pattern"
    end
  | ISimpl :: ?pats => simpl; iCodestructCohypFindPat Hgo pat found pats
  (* | IClear ?H :: ?pats => iClear H; iDestructHypFindPat Hgo pat found pats *)
  (* | IClearFrame ?H :: ?pats => iFrame H; iDestructHypFindPat Hgo pat found pats *)
  | ?pat1 :: ?pats =>
     lazymatch found with
     | false => iCodestructCohypGo Hgo pat pat1; iCodestructCohypFindPat Hgo pat true pats
     | true => fail "iDestruct:" pat "should contain exactly one proper introduction pattern"
     end
  end.
Tactic Notation "iCodestruct" constr(H) "as" constr(pat) :=
  let pats := intro_pat.parse pat in iCodestructCohypFindPat H pat false pats.
