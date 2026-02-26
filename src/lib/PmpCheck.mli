open Base1
open Bitvector
open Datatypes

type coq_PmpEntryCfg = (coq_Pmpcfg_ent, coq_Xlenbits) prod

type coq_PmpAddrRange = (coq_Xlenbits, coq_Xlenbits) prod option

val pmp_addr_range :
  coq_Pmpcfg_ent -> coq_Xlenbits -> coq_Xlenbits -> coq_PmpAddrRange

val pmp_match_addr :
  coq_Xlenbits -> coq_Xlenbits -> coq_PmpAddrRange -> coq_PmpAddrMatch

val pmp_match_entry :
  coq_Xlenbits -> coq_Xlenbits -> coq_Privilege -> coq_Pmpcfg_ent ->
  coq_Xlenbits -> coq_Xlenbits -> coq_PmpMatch

val decide_access_pmp_perm : coq_AccessType -> coq_PmpCfgPerm -> bool

val pmp_get_RWX : coq_Pmpcfg_ent -> coq_Privilege -> coq_PmpCfgPerm

val pmp_get_perms : coq_Pmpcfg_ent -> coq_Privilege -> coq_PmpCfgPerm

val pmp_check_rec :
  coq_Xlenbits -> coq_Xlenbits -> coq_Xlenbits -> coq_PmpEntryCfg list ->
  coq_Privilege -> coq_AccessType -> bool

val pmp_check_aux :
  coq_Xlenbits -> coq_Xlenbits -> coq_Xlenbits -> coq_PmpEntryCfg list ->
  coq_Privilege -> coq_AccessType -> bool
