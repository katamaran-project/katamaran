open Base1
open Bitvector
open Datatypes

type coq_PmpEntryCfg = (coq_Pmpcfg_ent, coq_Xlenbits) prod

type coq_PmpAddrRange = (coq_Xlenbits, coq_Xlenbits) prod option

(** val pmp_addr_range :
    coq_Pmpcfg_ent -> coq_Xlenbits -> coq_Xlenbits -> coq_PmpAddrRange **)

let pmp_addr_range cfg pmpaddr prev_pmpaddr =
  match cfg.coq_A with
  | OFF -> None
  | TOR -> Some (Coq_pair (prev_pmpaddr, pmpaddr))

(** val pmp_match_addr :
    coq_Xlenbits -> coq_Xlenbits -> coq_PmpAddrRange -> coq_PmpAddrMatch **)

let pmp_match_addr a width = function
| Some p ->
  let Coq_pair (lo, hi) = p in
  (match Coq_bv.ultb xlenbits hi lo with
   | Coq_true -> PMP_NoMatch
   | Coq_false ->
     (match match Coq_bv.uleb xlenbits (Coq_bv.add xlenbits a width) lo with
            | Coq_true -> Coq_true
            | Coq_false -> Coq_bv.uleb xlenbits hi a with
      | Coq_true -> PMP_NoMatch
      | Coq_false ->
        (match match Coq_bv.uleb xlenbits lo a with
               | Coq_true ->
                 Coq_bv.uleb xlenbits (Coq_bv.add xlenbits a width) hi
               | Coq_false -> Coq_false with
         | Coq_true -> PMP_Match
         | Coq_false -> PMP_PartialMatch)))
| None -> PMP_NoMatch

(** val pmp_match_entry :
    coq_Xlenbits -> coq_Xlenbits -> coq_Privilege -> coq_Pmpcfg_ent ->
    coq_Xlenbits -> coq_Xlenbits -> coq_PmpMatch **)

let pmp_match_entry a width _ cfg lo hi =
  let rng = pmp_addr_range cfg hi lo in
  (match pmp_match_addr a width rng with
   | PMP_NoMatch -> PMP_Continue
   | PMP_PartialMatch -> PMP_Fail
   | PMP_Match -> PMP_Success)

(** val decide_access_pmp_perm : coq_AccessType -> coq_PmpCfgPerm -> bool **)

let decide_access_pmp_perm a p =
  match a with
  | Read ->
    (match p with
     | PmpO -> Coq_false
     | PmpW -> Coq_false
     | PmpX -> Coq_false
     | PmpWX -> Coq_false
     | _ -> Coq_true)
  | Write ->
    (match p with
     | PmpO -> Coq_false
     | PmpR -> Coq_false
     | PmpX -> Coq_false
     | PmpRX -> Coq_false
     | _ -> Coq_true)
  | ReadWrite ->
    (match p with
     | PmpRW -> Coq_true
     | PmpRWX -> Coq_true
     | _ -> Coq_false)
  | Execute ->
    (match p with
     | PmpO -> Coq_false
     | PmpR -> Coq_false
     | PmpW -> Coq_false
     | PmpRW -> Coq_false
     | _ -> Coq_true)

(** val pmp_get_RWX : coq_Pmpcfg_ent -> coq_Privilege -> coq_PmpCfgPerm **)

let pmp_get_RWX cfg p =
  let { coq_L = l; coq_A = _; coq_X = x; coq_W = w; coq_R = r } = cfg in
  (match l with
   | Coq_true ->
     (match x with
      | Coq_true ->
        (match w with
         | Coq_true -> (match r with
                        | Coq_true -> PmpRWX
                        | Coq_false -> PmpWX)
         | Coq_false -> (match r with
                         | Coq_true -> PmpRX
                         | Coq_false -> PmpX))
      | Coq_false ->
        (match w with
         | Coq_true -> (match r with
                        | Coq_true -> PmpRW
                        | Coq_false -> PmpW)
         | Coq_false -> (match r with
                         | Coq_true -> PmpR
                         | Coq_false -> PmpO)))
   | Coq_false ->
     (match p with
      | User ->
        (match x with
         | Coq_true ->
           (match w with
            | Coq_true ->
              (match r with
               | Coq_true -> PmpRWX
               | Coq_false -> PmpWX)
            | Coq_false ->
              (match r with
               | Coq_true -> PmpRX
               | Coq_false -> PmpX))
         | Coq_false ->
           (match w with
            | Coq_true -> (match r with
                           | Coq_true -> PmpRW
                           | Coq_false -> PmpW)
            | Coq_false -> (match r with
                            | Coq_true -> PmpR
                            | Coq_false -> PmpO)))
      | Machine -> PmpRWX))

(** val pmp_get_perms : coq_Pmpcfg_ent -> coq_Privilege -> coq_PmpCfgPerm **)

let pmp_get_perms cfg p = match p with
| User -> pmp_get_RWX cfg p
| Machine ->
  (match cfg.coq_L with
   | Coq_true -> pmp_get_RWX cfg p
   | Coq_false -> PmpRWX)

(** val pmp_check_rec :
    coq_Xlenbits -> coq_Xlenbits -> coq_Xlenbits -> coq_PmpEntryCfg list ->
    coq_Privilege -> coq_AccessType -> bool **)

let rec pmp_check_rec a width lo entries p acc =
  match entries with
  | [] -> (match p with
           | User -> Coq_false
           | Machine -> Coq_true)
  | p0::entries0 ->
    let Coq_pair (cfg, hi) = p0 in
    (match pmp_match_entry a width p cfg lo hi with
     | PMP_Success -> decide_access_pmp_perm acc (pmp_get_perms cfg p)
     | PMP_Continue -> pmp_check_rec a width hi entries0 p acc
     | PMP_Fail -> Coq_false)

(** val pmp_check_aux :
    coq_Xlenbits -> coq_Xlenbits -> coq_Xlenbits -> coq_PmpEntryCfg list ->
    coq_Privilege -> coq_AccessType -> bool **)

let pmp_check_aux =
  pmp_check_rec
