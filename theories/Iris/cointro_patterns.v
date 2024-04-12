From stdpp Require Export strings.
From iris.proofmode Require Import base tokens.
From iris.prelude Require Import options.

Inductive goal_kind := GSpatial | GModal | GIntuitionistic.

Record cointro_goal := SpecGoal {
  cointro_goal_kind : goal_kind;
  cointro_goal_negate : bool;
  cointro_goal_hyps : list ident
}.

Inductive cointro_pat :=
  | SDrop : cointro_pat 
  | SFrame : ident → list cointro_pat → cointro_pat
  | SFrameByName : ident → list cointro_pat → cointro_pat
  | SPureGoal (perform_done : bool) : cointro_pat
  | SCoHyp : ident -> cointro_pat
  | SSplitGoal : cointro_goal → cointro_pat
  | SRefl : cointro_pat
  | SList : list (cointro_pat) -> cointro_pat
.

(* Definition goal_kind_modal (k : goal_kind) : bool := *)
(*   match k with GModal => true | _ => false end. *)
(* Definition cointro_pat_modal (p : cointro_pat) : bool := *)
(*   match p with *)
(*   | SSplitGoal g => goal_kind_modal (cointro_goal_kind g) *)
(*   | _ => false *)
(*   end. *)

Module cointro_pat.
Inductive stack_item :=
  | StPat : cointro_pat → stack_item
  | StFrame : string → stack_item
  | StList : stack_item.
Notation stack := (list stack_item).

Fixpoint close (k : stack) (ps : list cointro_pat) : option (list cointro_pat) :=
  match k with
  | [] => Some ps
  | StPat p :: k => close k (p :: ps)
  | StFrame _ :: _ => None
  | StList :: _ => None
  end.

Fixpoint close_ident (k : stack) (ps : list cointro_pat) : option stack :=
  match k with
  | [] => None
  | StPat p :: k => close_ident k (p :: ps)
  | StFrame s :: k => Some (StPat (SFrame s ps) :: k)
  | StList :: k => Some (StPat (SList ps) :: k)
  end.

Fixpoint parse_go (ts : list token) (k : stack) : option (list cointro_pat) :=
  match ts with
  | [] => close k []
  | TParenL :: ts => parse_go ts (StList :: k)
  | TParenR :: ts => k ← close_ident k []; parse_go ts k
  | TName s :: ts => parse_go ts (StPat (SCoHyp s) :: k)
  | TPure x :: ts => parse_go ts (StPat (SPureGoal false) :: k)
  | TBracketL :: TPure None :: TBracketR :: ts =>
     parse_go ts (StPat (SPureGoal false) :: k)
  | TBracketL :: TPure None :: TDone :: TBracketR :: ts =>
     parse_go ts (StPat (SPureGoal true) :: k)
  | TBracketL :: TIntuitionistic :: ts => parse_goal ts GIntuitionistic false [] k
  | TBracketL :: TModal :: ts => parse_goal ts GModal false [] k
  | TBracketL :: ts => parse_goal ts GSpatial false [] k
  | _ => None
  end
with parse_goal (ts : list token)
    (ki : goal_kind) (neg : bool) (hyps : list ident)
    (k : stack) : option (list cointro_pat) :=
  match ts with
  | TName s :: ts => parse_goal ts ki neg (INamed s :: hyps) k
  | TMinus :: ts =>
      if decide (¬neg ∧ hyps = [])
      then parse_goal ts ki true hyps k
      else None
  | TBracketR :: ts =>
     parse_go ts (StPat (SSplitGoal (SpecGoal ki neg (reverse hyps))) :: k)
  | _ => None
  end.
Definition parse (s : string) : option (list cointro_pat) :=
  parse_go (tokenize s) [].

Ltac parse s :=
  lazymatch type of s with
  | list cointro_pat => s
  | cointro_pat => constr:([s])
  | string =>
     lazymatch eval vm_compute in (parse s) with
     | Some ?pats => pats
     | _ => fail "cointro_pat.parse: cannot parse" s "as a cointroduction pattern"
     end
  | ident => constr:([SCoHyp s])
  | ?X => fail "cointro_pat.parse: the term" s
     "is expected to be a cointroduction pattern"
     "(usually a string),"
     "but has unexpected type" X
  end.
End cointro_pat.
