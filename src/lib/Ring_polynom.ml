open BinInt
open BinList
open BinNat
open BinNums
open BinPos
open Datatypes
open List

type 'c coq_Pol =
| Pc of 'c
| Pinj of positive * 'c coq_Pol
| PX of 'c coq_Pol * positive * 'c coq_Pol

(** val coq_P0 : 'a1 -> 'a1 coq_Pol **)

let coq_P0 cO =
  Pc cO

(** val coq_P1 : 'a1 -> 'a1 coq_Pol **)

let coq_P1 cI =
  Pc cI

(** val coq_Peq :
    ('a1 -> 'a1 -> bool) -> 'a1 coq_Pol -> 'a1 coq_Pol -> bool **)

let rec coq_Peq ceqb p p' =
  match p with
  | Pc c -> (match p' with
             | Pc c' -> ceqb c c'
             | _ -> Coq_false)
  | Pinj (j, q) ->
    (match p' with
     | Pinj (j', q') ->
       (match Pos.compare j j' with
        | Eq -> coq_Peq ceqb q q'
        | _ -> Coq_false)
     | _ -> Coq_false)
  | PX (p0, i, q) ->
    (match p' with
     | PX (p'0, i', q') ->
       (match Pos.compare i i' with
        | Eq ->
          (match coq_Peq ceqb p0 p'0 with
           | Coq_true -> coq_Peq ceqb q q'
           | Coq_false -> Coq_false)
        | _ -> Coq_false)
     | _ -> Coq_false)

(** val mkPinj : positive -> 'a1 coq_Pol -> 'a1 coq_Pol **)

let mkPinj j p = match p with
| Pc _ -> p
| Pinj (j', q) -> Pinj ((Pos.add j j'), q)
| PX (_, _, _) -> Pinj (j, p)

(** val mkPinj_pred : positive -> 'a1 coq_Pol -> 'a1 coq_Pol **)

let mkPinj_pred j p =
  match j with
  | Coq_xI j0 -> Pinj ((Coq_xO j0), p)
  | Coq_xO j0 -> Pinj ((Pos.pred_double j0), p)
  | Coq_xH -> p

(** val mkPX :
    'a1 -> ('a1 -> 'a1 -> bool) -> 'a1 coq_Pol -> positive -> 'a1 coq_Pol ->
    'a1 coq_Pol **)

let mkPX cO ceqb p i q =
  match p with
  | Pc c ->
    (match ceqb c cO with
     | Coq_true -> mkPinj Coq_xH q
     | Coq_false -> PX (p, i, q))
  | Pinj (_, _) -> PX (p, i, q)
  | PX (p', i', q') ->
    (match coq_Peq ceqb q' (coq_P0 cO) with
     | Coq_true -> PX (p', (Pos.add i' i), q)
     | Coq_false -> PX (p, i, q))

(** val mkXi : 'a1 -> 'a1 -> positive -> 'a1 coq_Pol **)

let mkXi cO cI i =
  PX ((coq_P1 cI), i, (coq_P0 cO))

(** val mkX : 'a1 -> 'a1 -> 'a1 coq_Pol **)

let mkX cO cI =
  mkXi cO cI Coq_xH

(** val coq_Popp : ('a1 -> 'a1) -> 'a1 coq_Pol -> 'a1 coq_Pol **)

let rec coq_Popp copp = function
| Pc c -> Pc (copp c)
| Pinj (j, q) -> Pinj (j, (coq_Popp copp q))
| PX (p0, i, q) -> PX ((coq_Popp copp p0), i, (coq_Popp copp q))

(** val coq_PaddC :
    ('a1 -> 'a1 -> 'a1) -> 'a1 coq_Pol -> 'a1 -> 'a1 coq_Pol **)

let rec coq_PaddC cadd p c =
  match p with
  | Pc c1 -> Pc (cadd c1 c)
  | Pinj (j, q) -> Pinj (j, (coq_PaddC cadd q c))
  | PX (p0, i, q) -> PX (p0, i, (coq_PaddC cadd q c))

(** val coq_PsubC :
    ('a1 -> 'a1 -> 'a1) -> 'a1 coq_Pol -> 'a1 -> 'a1 coq_Pol **)

let rec coq_PsubC csub p c =
  match p with
  | Pc c1 -> Pc (csub c1 c)
  | Pinj (j, q) -> Pinj (j, (coq_PsubC csub q c))
  | PX (p0, i, q) -> PX (p0, i, (coq_PsubC csub q c))

(** val coq_PaddI :
    ('a1 -> 'a1 -> 'a1) -> ('a1 coq_Pol -> 'a1 coq_Pol -> 'a1 coq_Pol) -> 'a1
    coq_Pol -> positive -> 'a1 coq_Pol -> 'a1 coq_Pol **)

let rec coq_PaddI cadd pop q j = function
| Pc c -> mkPinj j (coq_PaddC cadd q c)
| Pinj (j', q') ->
  (match Z.pos_sub j' j with
   | Z0 -> mkPinj j (pop q' q)
   | Zpos k -> mkPinj j (pop (Pinj (k, q')) q)
   | Zneg k -> mkPinj j' (coq_PaddI cadd pop q k q'))
| PX (p0, i, q') ->
  (match j with
   | Coq_xI j0 -> PX (p0, i, (coq_PaddI cadd pop q (Coq_xO j0) q'))
   | Coq_xO j0 -> PX (p0, i, (coq_PaddI cadd pop q (Pos.pred_double j0) q'))
   | Coq_xH -> PX (p0, i, (pop q' q)))

(** val coq_PsubI :
    ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 coq_Pol -> 'a1 coq_Pol -> 'a1
    coq_Pol) -> 'a1 coq_Pol -> positive -> 'a1 coq_Pol -> 'a1 coq_Pol **)

let rec coq_PsubI cadd copp pop q j = function
| Pc c -> mkPinj j (coq_PaddC cadd (coq_Popp copp q) c)
| Pinj (j', q') ->
  (match Z.pos_sub j' j with
   | Z0 -> mkPinj j (pop q' q)
   | Zpos k -> mkPinj j (pop (Pinj (k, q')) q)
   | Zneg k -> mkPinj j' (coq_PsubI cadd copp pop q k q'))
| PX (p0, i, q') ->
  (match j with
   | Coq_xI j0 -> PX (p0, i, (coq_PsubI cadd copp pop q (Coq_xO j0) q'))
   | Coq_xO j0 ->
     PX (p0, i, (coq_PsubI cadd copp pop q (Pos.pred_double j0) q'))
   | Coq_xH -> PX (p0, i, (pop q' q)))

(** val coq_PaddX :
    'a1 -> ('a1 -> 'a1 -> bool) -> ('a1 coq_Pol -> 'a1 coq_Pol -> 'a1
    coq_Pol) -> 'a1 coq_Pol -> positive -> 'a1 coq_Pol -> 'a1 coq_Pol **)

let rec coq_PaddX cO ceqb pop p' i' p = match p with
| Pc _ -> PX (p', i', p)
| Pinj (j, q') ->
  (match j with
   | Coq_xI j0 -> PX (p', i', (Pinj ((Coq_xO j0), q')))
   | Coq_xO j0 -> PX (p', i', (Pinj ((Pos.pred_double j0), q')))
   | Coq_xH -> PX (p', i', q'))
| PX (p0, i, q') ->
  (match Z.pos_sub i i' with
   | Z0 -> mkPX cO ceqb (pop p0 p') i q'
   | Zpos k -> mkPX cO ceqb (pop (PX (p0, k, (coq_P0 cO))) p') i' q'
   | Zneg k -> mkPX cO ceqb (coq_PaddX cO ceqb pop p' k p0) i q')

(** val coq_PsubX :
    'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 coq_Pol -> 'a1
    coq_Pol -> 'a1 coq_Pol) -> 'a1 coq_Pol -> positive -> 'a1 coq_Pol -> 'a1
    coq_Pol **)

let rec coq_PsubX cO copp ceqb pop p' i' p = match p with
| Pc _ -> PX ((coq_Popp copp p'), i', p)
| Pinj (j, q') ->
  (match j with
   | Coq_xI j0 -> PX ((coq_Popp copp p'), i', (Pinj ((Coq_xO j0), q')))
   | Coq_xO j0 ->
     PX ((coq_Popp copp p'), i', (Pinj ((Pos.pred_double j0), q')))
   | Coq_xH -> PX ((coq_Popp copp p'), i', q'))
| PX (p0, i, q') ->
  (match Z.pos_sub i i' with
   | Z0 -> mkPX cO ceqb (pop p0 p') i q'
   | Zpos k -> mkPX cO ceqb (pop (PX (p0, k, (coq_P0 cO))) p') i' q'
   | Zneg k -> mkPX cO ceqb (coq_PsubX cO copp ceqb pop p' k p0) i q')

(** val coq_Padd :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 coq_Pol -> 'a1
    coq_Pol -> 'a1 coq_Pol **)

let rec coq_Padd cO cadd ceqb p = function
| Pc c' -> coq_PaddC cadd p c'
| Pinj (j', q') -> coq_PaddI cadd (coq_Padd cO cadd ceqb) q' j' p
| PX (p'0, i', q') ->
  (match p with
   | Pc c -> PX (p'0, i', (coq_PaddC cadd q' c))
   | Pinj (j, q) ->
     (match j with
      | Coq_xI j0 ->
        PX (p'0, i', (coq_Padd cO cadd ceqb (Pinj ((Coq_xO j0), q)) q'))
      | Coq_xO j0 ->
        PX (p'0, i',
          (coq_Padd cO cadd ceqb (Pinj ((Pos.pred_double j0), q)) q'))
      | Coq_xH -> PX (p'0, i', (coq_Padd cO cadd ceqb q q')))
   | PX (p0, i, q) ->
     (match Z.pos_sub i i' with
      | Z0 ->
        mkPX cO ceqb (coq_Padd cO cadd ceqb p0 p'0) i
          (coq_Padd cO cadd ceqb q q')
      | Zpos k ->
        mkPX cO ceqb (coq_Padd cO cadd ceqb (PX (p0, k, (coq_P0 cO))) p'0) i'
          (coq_Padd cO cadd ceqb q q')
      | Zneg k ->
        mkPX cO ceqb (coq_PaddX cO ceqb (coq_Padd cO cadd ceqb) p'0 k p0) i
          (coq_Padd cO cadd ceqb q q')))

(** val coq_Psub :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1
    -> 'a1 -> bool) -> 'a1 coq_Pol -> 'a1 coq_Pol -> 'a1 coq_Pol **)

let rec coq_Psub cO cadd csub copp ceqb p = function
| Pc c' -> coq_PsubC csub p c'
| Pinj (j', q') ->
  coq_PsubI cadd copp (coq_Psub cO cadd csub copp ceqb) q' j' p
| PX (p'0, i', q') ->
  (match p with
   | Pc c ->
     PX ((coq_Popp copp p'0), i', (coq_PaddC cadd (coq_Popp copp q') c))
   | Pinj (j, q) ->
     (match j with
      | Coq_xI j0 ->
        PX ((coq_Popp copp p'0), i',
          (coq_Psub cO cadd csub copp ceqb (Pinj ((Coq_xO j0), q)) q'))
      | Coq_xO j0 ->
        PX ((coq_Popp copp p'0), i',
          (coq_Psub cO cadd csub copp ceqb (Pinj ((Pos.pred_double j0), q))
            q'))
      | Coq_xH ->
        PX ((coq_Popp copp p'0), i', (coq_Psub cO cadd csub copp ceqb q q')))
   | PX (p0, i, q) ->
     (match Z.pos_sub i i' with
      | Z0 ->
        mkPX cO ceqb (coq_Psub cO cadd csub copp ceqb p0 p'0) i
          (coq_Psub cO cadd csub copp ceqb q q')
      | Zpos k ->
        mkPX cO ceqb
          (coq_Psub cO cadd csub copp ceqb (PX (p0, k, (coq_P0 cO))) p'0) i'
          (coq_Psub cO cadd csub copp ceqb q q')
      | Zneg k ->
        mkPX cO ceqb
          (coq_PsubX cO copp ceqb (coq_Psub cO cadd csub copp ceqb) p'0 k p0)
          i (coq_Psub cO cadd csub copp ceqb q q')))

(** val coq_PmulC_aux :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 coq_Pol -> 'a1
    -> 'a1 coq_Pol **)

let rec coq_PmulC_aux cO cmul ceqb p c =
  match p with
  | Pc c' -> Pc (cmul c' c)
  | Pinj (j, q) -> mkPinj j (coq_PmulC_aux cO cmul ceqb q c)
  | PX (p0, i, q) ->
    mkPX cO ceqb (coq_PmulC_aux cO cmul ceqb p0 c) i
      (coq_PmulC_aux cO cmul ceqb q c)

(** val coq_PmulC :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 coq_Pol
    -> 'a1 -> 'a1 coq_Pol **)

let coq_PmulC cO cI cmul ceqb p c =
  match ceqb c cO with
  | Coq_true -> coq_P0 cO
  | Coq_false ->
    (match ceqb c cI with
     | Coq_true -> p
     | Coq_false -> coq_PmulC_aux cO cmul ceqb p c)

(** val coq_PmulI :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 coq_Pol
    -> 'a1 coq_Pol -> 'a1 coq_Pol) -> 'a1 coq_Pol -> positive -> 'a1 coq_Pol
    -> 'a1 coq_Pol **)

let rec coq_PmulI cO cI cmul ceqb pmul q j = function
| Pc c -> mkPinj j (coq_PmulC cO cI cmul ceqb q c)
| Pinj (j', q') ->
  (match Z.pos_sub j' j with
   | Z0 -> mkPinj j (pmul q' q)
   | Zpos k -> mkPinj j (pmul (Pinj (k, q')) q)
   | Zneg k -> mkPinj j' (coq_PmulI cO cI cmul ceqb pmul q k q'))
| PX (p', i', q') ->
  (match j with
   | Coq_xI j' ->
     mkPX cO ceqb (coq_PmulI cO cI cmul ceqb pmul q j p') i'
       (coq_PmulI cO cI cmul ceqb pmul q (Coq_xO j') q')
   | Coq_xO j' ->
     mkPX cO ceqb (coq_PmulI cO cI cmul ceqb pmul q j p') i'
       (coq_PmulI cO cI cmul ceqb pmul q (Pos.pred_double j') q')
   | Coq_xH ->
     mkPX cO ceqb (coq_PmulI cO cI cmul ceqb pmul q Coq_xH p') i' (pmul q' q))

(** val coq_Pmul :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> bool) -> 'a1 coq_Pol -> 'a1 coq_Pol -> 'a1 coq_Pol **)

let rec coq_Pmul cO cI cadd cmul ceqb p p'' = match p'' with
| Pc c -> coq_PmulC cO cI cmul ceqb p c
| Pinj (j', q') ->
  coq_PmulI cO cI cmul ceqb (coq_Pmul cO cI cadd cmul ceqb) q' j' p
| PX (p', i', q') ->
  (match p with
   | Pc c -> coq_PmulC cO cI cmul ceqb p'' c
   | Pinj (j, q) ->
     let qQ' =
       match j with
       | Coq_xI j0 -> coq_Pmul cO cI cadd cmul ceqb (Pinj ((Coq_xO j0), q)) q'
       | Coq_xO j0 ->
         coq_Pmul cO cI cadd cmul ceqb (Pinj ((Pos.pred_double j0), q)) q'
       | Coq_xH -> coq_Pmul cO cI cadd cmul ceqb q q'
     in
     mkPX cO ceqb (coq_Pmul cO cI cadd cmul ceqb p p') i' qQ'
   | PX (p0, i, q) ->
     let qQ' = coq_Pmul cO cI cadd cmul ceqb q q' in
     let pQ' =
       coq_PmulI cO cI cmul ceqb (coq_Pmul cO cI cadd cmul ceqb) q' Coq_xH p0
     in
     let qP' = coq_Pmul cO cI cadd cmul ceqb (mkPinj Coq_xH q) p' in
     let pP' = coq_Pmul cO cI cadd cmul ceqb p0 p' in
     coq_Padd cO cadd ceqb
       (mkPX cO ceqb
         (coq_Padd cO cadd ceqb (mkPX cO ceqb pP' i (coq_P0 cO)) qP') i'
         (coq_P0 cO))
       (mkPX cO ceqb pQ' i qQ'))

type 'c coq_PExpr =
| PEO
| PEI
| PEc of 'c
| PEX of positive
| PEadd of 'c coq_PExpr * 'c coq_PExpr
| PEsub of 'c coq_PExpr * 'c coq_PExpr
| PEmul of 'c coq_PExpr * 'c coq_PExpr
| PEopp of 'c coq_PExpr
| PEpow of 'c coq_PExpr * coq_N

(** val mk_X : 'a1 -> 'a1 -> positive -> 'a1 coq_Pol **)

let mk_X cO cI j =
  mkPinj_pred j (mkX cO cI)

(** val coq_PEeval :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> 'a1) -> ('a1 -> 'a1) -> ('a2 -> 'a1) -> (coq_N -> 'a3) -> ('a1 -> 'a3
    -> 'a1) -> 'a1 list -> 'a2 coq_PExpr -> 'a1 **)

let rec coq_PEeval rO rI radd rmul rsub ropp phi cp_phi rpow l = function
| PEO -> rO
| PEI -> rI
| PEc c -> phi c
| PEX j -> nth rO j l
| PEadd (pe1, pe2) ->
  radd (coq_PEeval rO rI radd rmul rsub ropp phi cp_phi rpow l pe1)
    (coq_PEeval rO rI radd rmul rsub ropp phi cp_phi rpow l pe2)
| PEsub (pe1, pe2) ->
  rsub (coq_PEeval rO rI radd rmul rsub ropp phi cp_phi rpow l pe1)
    (coq_PEeval rO rI radd rmul rsub ropp phi cp_phi rpow l pe2)
| PEmul (pe1, pe2) ->
  rmul (coq_PEeval rO rI radd rmul rsub ropp phi cp_phi rpow l pe1)
    (coq_PEeval rO rI radd rmul rsub ropp phi cp_phi rpow l pe2)
| PEopp pe1 ->
  ropp (coq_PEeval rO rI radd rmul rsub ropp phi cp_phi rpow l pe1)
| PEpow (pe1, n) ->
  rpow (coq_PEeval rO rI radd rmul rsub ropp phi cp_phi rpow l pe1) (cp_phi n)

(** val coq_Ppow_pos :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> bool) -> ('a1 coq_Pol -> 'a1 coq_Pol) -> 'a1 coq_Pol -> 'a1 coq_Pol ->
    positive -> 'a1 coq_Pol **)

let rec coq_Ppow_pos cO cI cadd cmul ceqb subst_l res p = function
| Coq_xI p1 ->
  subst_l
    (coq_Pmul cO cI cadd cmul ceqb
      (coq_Ppow_pos cO cI cadd cmul ceqb subst_l
        (coq_Ppow_pos cO cI cadd cmul ceqb subst_l res p p1) p p1)
      p)
| Coq_xO p1 ->
  coq_Ppow_pos cO cI cadd cmul ceqb subst_l
    (coq_Ppow_pos cO cI cadd cmul ceqb subst_l res p p1) p p1
| Coq_xH -> subst_l (coq_Pmul cO cI cadd cmul ceqb res p)

(** val coq_Ppow_N :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> bool) -> ('a1 coq_Pol -> 'a1 coq_Pol) -> 'a1 coq_Pol -> coq_N -> 'a1
    coq_Pol **)

let coq_Ppow_N cO cI cadd cmul ceqb subst_l p = function
| N0 -> coq_P1 cI
| Npos p0 -> coq_Ppow_pos cO cI cadd cmul ceqb subst_l (coq_P1 cI) p p0

(** val norm_aux :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 coq_PExpr -> 'a1
    coq_Pol **)

let rec norm_aux cO cI cadd cmul csub copp ceqb = function
| PEO -> Pc cO
| PEI -> Pc cI
| PEc c -> Pc c
| PEX j -> mk_X cO cI j
| PEadd (pe1, pe2) ->
  (match pe1 with
   | PEopp pe3 ->
     coq_Psub cO cadd csub copp ceqb
       (norm_aux cO cI cadd cmul csub copp ceqb pe2)
       (norm_aux cO cI cadd cmul csub copp ceqb pe3)
   | _ ->
     (match pe2 with
      | PEopp pe3 ->
        coq_Psub cO cadd csub copp ceqb
          (norm_aux cO cI cadd cmul csub copp ceqb pe1)
          (norm_aux cO cI cadd cmul csub copp ceqb pe3)
      | _ ->
        coq_Padd cO cadd ceqb (norm_aux cO cI cadd cmul csub copp ceqb pe1)
          (norm_aux cO cI cadd cmul csub copp ceqb pe2)))
| PEsub (pe1, pe2) ->
  coq_Psub cO cadd csub copp ceqb
    (norm_aux cO cI cadd cmul csub copp ceqb pe1)
    (norm_aux cO cI cadd cmul csub copp ceqb pe2)
| PEmul (pe1, pe2) ->
  coq_Pmul cO cI cadd cmul ceqb (norm_aux cO cI cadd cmul csub copp ceqb pe1)
    (norm_aux cO cI cadd cmul csub copp ceqb pe2)
| PEopp pe1 -> coq_Popp copp (norm_aux cO cI cadd cmul csub copp ceqb pe1)
| PEpow (pe1, n) ->
  coq_Ppow_N cO cI cadd cmul ceqb (fun p -> p)
    (norm_aux cO cI cadd cmul csub copp ceqb pe1) n

(** val mkmult_rec :
    ('a1 -> 'a1 -> positive -> 'a1) -> 'a1 -> ('a1, positive) prod list -> 'a1 **)

let rec mkmult_rec mkmult_pow0 r = function
| Coq_nil -> r
| Coq_cons (p0, t) ->
  let Coq_pair (x, p) = p0 in mkmult_rec mkmult_pow0 (mkmult_pow0 r x p) t

(** val mkmult1 :
    'a1 -> ('a1 -> positive -> 'a1) -> ('a1 -> 'a1 -> positive -> 'a1) ->
    ('a1, positive) prod list -> 'a1 **)

let mkmult1 rI mkpow0 mkmult_pow0 = function
| Coq_nil -> rI
| Coq_cons (y, t) ->
  let Coq_pair (x, p) = y in mkmult_rec mkmult_pow0 (mkpow0 x p) t

(** val mkmultm1 :
    'a1 -> ('a1 -> 'a1) -> ('a1 -> positive -> 'a1) -> ('a1 -> 'a1 ->
    positive -> 'a1) -> ('a1, positive) prod list -> 'a1 **)

let mkmultm1 rI ropp mkopp_pow0 mkmult_pow0 = function
| Coq_nil -> ropp rI
| Coq_cons (y, t) ->
  let Coq_pair (x, p) = y in mkmult_rec mkmult_pow0 (mkopp_pow0 x p) t

(** val mkmult_c_pos :
    'a1 -> 'a2 -> ('a2 -> 'a2 -> bool) -> ('a2 -> 'a1) -> ('a1 -> positive ->
    'a1) -> ('a1 -> 'a1 -> positive -> 'a1) -> 'a2 -> ('a1, positive) prod
    list -> 'a1 **)

let mkmult_c_pos rI cI ceqb phi mkpow0 mkmult_pow0 c lm =
  match ceqb c cI with
  | Coq_true -> mkmult1 rI mkpow0 mkmult_pow0 (rev' lm)
  | Coq_false -> mkmult_rec mkmult_pow0 (phi c) (rev' lm)

(** val mkmult_c :
    'a1 -> ('a1 -> 'a1) -> 'a2 -> ('a2 -> 'a2 -> bool) -> ('a2 -> 'a1) ->
    ('a2 -> 'a2 option) -> ('a1 -> positive -> 'a1) -> ('a1 -> positive ->
    'a1) -> ('a1 -> 'a1 -> positive -> 'a1) -> 'a2 -> ('a1, positive) prod
    list -> 'a1 **)

let mkmult_c rI ropp cI ceqb phi get_sign mkpow0 mkopp_pow0 mkmult_pow0 c lm =
  match get_sign c with
  | Some c' ->
    (match ceqb c' cI with
     | Coq_true -> mkmultm1 rI ropp mkopp_pow0 mkmult_pow0 (rev' lm)
     | Coq_false -> mkmult_rec mkmult_pow0 (phi c) (rev' lm))
  | None -> mkmult_c_pos rI cI ceqb phi mkpow0 mkmult_pow0 c lm

(** val mkadd_mult :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a2 -> ('a2 -> 'a2
    -> bool) -> ('a2 -> 'a1) -> ('a2 -> 'a2 option) -> ('a1 -> positive ->
    'a1) -> ('a1 -> 'a1 -> positive -> 'a1) -> 'a1 -> 'a2 -> ('a1, positive)
    prod list -> 'a1 **)

let mkadd_mult rI radd rsub cI ceqb phi get_sign mkpow0 mkmult_pow0 rP c lm =
  match get_sign c with
  | Some c' -> rsub rP (mkmult_c_pos rI cI ceqb phi mkpow0 mkmult_pow0 c' lm)
  | None -> radd rP (mkmult_c_pos rI cI ceqb phi mkpow0 mkmult_pow0 c lm)

(** val add_pow_list :
    'a1 -> coq_N -> ('a1, positive) prod list -> ('a1, positive) prod list **)

let add_pow_list r n l =
  match n with
  | N0 -> l
  | Npos p -> Coq_cons ((Coq_pair (r, p)), l)

(** val add_mult_dev :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a2 -> 'a2 ->
    ('a2 -> 'a2 -> bool) -> ('a2 -> 'a1) -> ('a2 -> 'a2 option) -> ('a1 ->
    positive -> 'a1) -> ('a1 -> 'a1 -> positive -> 'a1) -> 'a1 -> 'a2 coq_Pol
    -> 'a1 list -> coq_N -> ('a1, positive) prod list -> 'a1 **)

let rec add_mult_dev rO rI radd rsub cO cI ceqb phi get_sign mkpow0 mkmult_pow0 rP p fv n lm =
  match p with
  | Pc c ->
    let lm0 = add_pow_list (hd rO fv) n lm in
    mkadd_mult rI radd rsub cI ceqb phi get_sign mkpow0 mkmult_pow0 rP c lm0
  | Pinj (j, q) ->
    add_mult_dev rO rI radd rsub cO cI ceqb phi get_sign mkpow0 mkmult_pow0
      rP q (jump j fv) N0 (add_pow_list (hd rO fv) n lm)
  | PX (p0, i, q) ->
    let rP0 =
      add_mult_dev rO rI radd rsub cO cI ceqb phi get_sign mkpow0 mkmult_pow0
        rP p0 fv (N.add (Npos i) n) lm
    in
    (match coq_Peq ceqb q (coq_P0 cO) with
     | Coq_true -> rP0
     | Coq_false ->
       add_mult_dev rO rI radd rsub cO cI ceqb phi get_sign mkpow0
         mkmult_pow0 rP0 q (tl fv) N0 (add_pow_list (hd rO fv) n lm))

(** val mult_dev :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1)
    -> 'a2 -> 'a2 -> ('a2 -> 'a2 -> bool) -> ('a2 -> 'a1) -> ('a2 -> 'a2
    option) -> ('a1 -> positive -> 'a1) -> ('a1 -> positive -> 'a1) -> ('a1
    -> 'a1 -> positive -> 'a1) -> 'a2 coq_Pol -> 'a1 list -> coq_N -> ('a1,
    positive) prod list -> 'a1 **)

let rec mult_dev rO rI radd rsub ropp cO cI ceqb phi get_sign mkpow0 mkopp_pow0 mkmult_pow0 p fv n lm =
  match p with
  | Pc c ->
    mkmult_c rI ropp cI ceqb phi get_sign mkpow0 mkopp_pow0 mkmult_pow0 c
      (add_pow_list (hd rO fv) n lm)
  | Pinj (j, q) ->
    mult_dev rO rI radd rsub ropp cO cI ceqb phi get_sign mkpow0 mkopp_pow0
      mkmult_pow0 q (jump j fv) N0 (add_pow_list (hd rO fv) n lm)
  | PX (p0, i, q) ->
    let rP =
      mult_dev rO rI radd rsub ropp cO cI ceqb phi get_sign mkpow0 mkopp_pow0
        mkmult_pow0 p0 fv (N.add (Npos i) n) lm
    in
    (match coq_Peq ceqb q (coq_P0 cO) with
     | Coq_true -> rP
     | Coq_false ->
       let lmq = add_pow_list (hd rO fv) n lm in
       add_mult_dev rO rI radd rsub cO cI ceqb phi get_sign mkpow0
         mkmult_pow0 rP q (tl fv) N0 lmq)

(** val coq_Pphi_avoid :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1)
    -> 'a2 -> 'a2 -> ('a2 -> 'a2 -> bool) -> ('a2 -> 'a1) -> ('a2 -> 'a2
    option) -> ('a1 -> positive -> 'a1) -> ('a1 -> positive -> 'a1) -> ('a1
    -> 'a1 -> positive -> 'a1) -> 'a1 list -> 'a2 coq_Pol -> 'a1 **)

let coq_Pphi_avoid rO rI radd rsub ropp cO cI ceqb phi get_sign mkpow0 mkopp_pow0 mkmult_pow0 fv p =
  mult_dev rO rI radd rsub ropp cO cI ceqb phi get_sign mkpow0 mkopp_pow0
    mkmult_pow0 p fv N0 Coq_nil

(** val mkmult_pow : ('a1 -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> positive -> 'a1 **)

let rec mkmult_pow rmul r x = function
| Coq_xI p0 -> mkmult_pow rmul (mkmult_pow rmul (rmul r x) x p0) x p0
| Coq_xO p0 -> mkmult_pow rmul (mkmult_pow rmul r x p0) x p0
| Coq_xH -> rmul r x

(** val mkpow : ('a1 -> 'a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

let mkpow rmul x = function
| Coq_xI p0 -> mkmult_pow rmul x x (Coq_xO p0)
| Coq_xO p0 -> mkmult_pow rmul x x (Pos.pred_double p0)
| Coq_xH -> x

(** val mkopp_pow :
    ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

let mkopp_pow rmul ropp x = function
| Coq_xI p0 -> mkmult_pow rmul (ropp x) x (Coq_xO p0)
| Coq_xO p0 -> mkmult_pow rmul (ropp x) x (Pos.pred_double p0)
| Coq_xH -> ropp x

(** val coq_Pphi_dev :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> 'a1) -> ('a1 -> 'a1) -> 'a2 -> 'a2 -> ('a2 -> 'a2 -> bool) -> ('a2 ->
    'a1) -> ('a2 -> 'a2 option) -> 'a1 list -> 'a2 coq_Pol -> 'a1 **)

let coq_Pphi_dev rO rI radd rmul rsub ropp cO cI ceqb phi get_sign =
  coq_Pphi_avoid rO rI radd rsub ropp cO cI ceqb phi get_sign (mkpow rmul)
    (mkopp_pow rmul ropp) (mkmult_pow rmul)
