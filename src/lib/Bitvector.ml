open BinInt
open BinNat
open BinNums
open Classes
open Datatypes
open ListDef
open Nat
open Base
open Finite
open List_numbers

type __ = Obj.t

module Coq_bv =
 struct
  type bv = coq_N
    (* singleton inductive, whose constructor was mk *)

  (** val bin : nat -> bv -> coq_N **)

  let bin _ b =
    b

  (** val eqb : nat -> bv -> bv -> bool **)

  let eqb _ =
    N.eqb

  (** val eqdec_bv : nat -> bv coq_EqDec **)

  let eqdec_bv _ =
    N.eq_dec

  (** val trunc : nat -> positive -> coq_N **)

  let rec trunc n p =
    match n with
    | O -> N0
    | S n0 ->
      (match p with
       | Coq_xI p0 -> N.succ_double (trunc n0 p0)
       | Coq_xO p0 -> N.double (trunc n0 p0)
       | Coq_xH -> Npos Coq_xH)

  (** val truncn : nat -> coq_N -> coq_N **)

  let truncn n = function
  | N0 -> N0
  | Npos p -> trunc n p

  (** val of_N : nat -> coq_N -> bv **)

  let of_N =
    truncn

  (** val of_nat : nat -> nat -> bv **)

  let of_nat n k =
    of_N n (N.of_nat k)

  (** val nil : bv **)

  let nil =
    N0

  (** val cons : nat -> bool -> bv -> bv **)

  let cons _ b xs =
    match b with
    | Coq_true -> N.succ_double xs
    | Coq_false -> N.double xs

  (** val bv_case : 'a1 -> (nat -> bool -> bv -> 'a1) -> nat -> bv -> 'a1 **)

  let bv_case pO pS n xs =
    match n with
    | O -> (match xs with
            | N0 -> pO
            | Npos _ -> assert false (* absurd case *))
    | S m ->
      (match xs with
       | N0 -> pS m Coq_false N0
       | Npos p ->
         (match p with
          | Coq_xI p0 -> pS m Coq_true (Npos p0)
          | Coq_xO p0 -> pS m Coq_false (Npos p0)
          | Coq_xH -> pS m Coq_true N0))

  (** val fold_right :
      (nat -> bool -> 'a1 -> 'a1) -> 'a1 -> nat -> bv -> 'a1 **)

  let rec fold_right c n m xs =
    bv_case n (fun k b x -> c k b (fold_right c n k x)) m xs

  (** val fold_left :
      (nat -> 'a1 -> bool -> 'a1) -> 'a1 -> nat -> bv -> 'a1 **)

  let rec fold_left c n m xs =
    bv_case n (fun k b xs0 -> fold_left (fun m0 -> c (S m0)) (c O n b) k xs0)
      m xs

  type coq_NilView =
  | Coq_nvnil

  type coq_ConsView =
  | Coq_cvcons of bool * bv

  (** val view : nat -> bv -> __ **)

  let view =
    bv_case (Obj.magic Coq_nvnil)
      (Obj.magic (fun _ x x0 -> Coq_cvcons (x, x0)))

  (** val app : nat -> nat -> bv -> bv -> bv **)

  let app m n xs ys =
    fold_right (fun m0 -> cons (add m0 n)) ys m xs

  type coq_AppView =
  | Coq_isapp of bv * bv

  (** val avcons : nat -> nat -> bool -> bv -> coq_AppView -> coq_AppView **)

  let avcons m _ b _ = function
  | Coq_isapp (xs, ys) -> Coq_isapp ((cons m b xs), ys)

  (** val appView : nat -> nat -> bv -> coq_AppView **)

  let rec appView m n x =
    match m with
    | O -> Coq_isapp (nil, x)
    | S m0 ->
      let Coq_cvcons (b, xs) = Obj.magic view (add (S m0) n) x in
      avcons m0 n b xs (appView m0 n xs)

  (** val zero : nat -> bv **)

  let zero _ =
    N0

  (** val one : nat -> bv **)

  let one = function
  | O -> N0
  | S _ -> Npos Coq_xH

  (** val onesp : nat -> positive **)

  let rec onesp = function
  | O -> Coq_xH
  | S n0 -> Coq_xI (onesp n0)

  (** val onesn : nat -> coq_N **)

  let onesn = function
  | O -> N0
  | S m -> Npos (onesp m)

  (** val ones : nat -> bv **)

  let ones =
    onesn

  (** val bv_inhabited : nat -> bv coq_Inhabited **)

  let bv_inhabited =
    zero

  (** val msbwithcarry : nat -> bool -> bv -> bool **)

  let msbwithcarry n c v =
    fold_left (fun _ _ m -> m) c n v

  (** val msb : nat -> bv -> bool **)

  let msb n v =
    msbwithcarry n Coq_false v

  (** val sext' : nat -> bv -> nat -> bv **)

  let sext' m v n =
    app m n v (match msb m v with
               | Coq_true -> ones n
               | Coq_false -> zero n)

  (** val zext' : nat -> bv -> nat -> bv **)

  let zext' m v n =
    app m n v (zero n)

  type coq_LeView = nat
    (* singleton inductive, whose constructor was is_le *)

  (** val leview : nat -> nat -> coq_LeView **)

  let rec leview m n =
    match m with
    | O -> n
    | S m' ->
      (match n with
       | O -> assert false (* absurd case *)
       | S n' -> leview m' n')

  (** val sext : nat -> bv -> nat -> bv **)

  let sext m v n =
    sext' m v (leview m n)

  (** val zext : nat -> bv -> nat -> bv **)

  let zext m v n =
    zext' m v (leview m n)

  (** val truncate : nat -> nat -> bv -> bv **)

  let truncate n m xs =
    let Coq_isapp (result, _) = appView m (leview m n) xs in result

  (** val unsigned : nat -> bv -> coq_Z **)

  let unsigned _ =
    Z.of_N

  (** val signed : nat -> bv -> coq_Z **)

  let signed n x =
    let u = unsigned n x in
    (match msb n x with
     | Coq_true -> Z.sub u (Z.pow (Zpos (Coq_xO Coq_xH)) (Z.of_nat n))
     | Coq_false -> u)

  (** val truncz : nat -> coq_Z -> coq_Z **)

  let truncz n y =
    Z.modulo y (Z.pow (Zpos (Coq_xO Coq_xH)) (Z.of_nat n))

  (** val of_Z : nat -> coq_Z -> bv **)

  let of_Z n x =
    of_N n (Z.to_N (truncz n x))

  (** val drop : nat -> nat -> bv -> bv **)

  let drop m n x =
    let Coq_isapp (_, ys) = appView m n x in ys

  (** val take : nat -> nat -> bv -> bv **)

  let take m n x =
    let Coq_isapp (xs, _) = appView m n x in xs

  (** val vector_subrange : nat -> nat -> nat -> bv -> bv **)

  let vector_subrange n start len bits =
    drop start len (take (add start len) (leview (add start len) n) bits)

  (** val update_vector_subrange : nat -> nat -> nat -> bv -> bv -> bv **)

  let update_vector_subrange n start len =
    let k = leview (add start len) n in
    (fun bits upd ->
    let Coq_isapp (xs, rest1) = appView (add start len) k bits in
    let Coq_isapp (rest2, _) = appView start len xs in
    app (add start len) k (app start len rest2 upd) rest1)

  (** val shiftr : nat -> nat -> bv -> bv -> bv **)

  let shiftr m n x y =
    of_Z m (Z.shiftr (unsigned m x) (unsigned n y))

  (** val shiftl : nat -> nat -> bv -> bv -> bv **)

  let shiftl m n x y =
    of_Z m (Z.shiftl (unsigned m x) (unsigned n y))

  (** val add : nat -> bv -> bv -> bv **)

  let add n x y =
    of_N n (N.add x y)

  (** val negate : nat -> bv -> bv **)

  let negate n x =
    of_N n (N.sub (N.pow (Npos (Coq_xO Coq_xH)) (N.of_nat n)) x)

  (** val sub : nat -> bv -> bv -> bv **)

  let sub n x y =
    add n x (negate n y)

  (** val mul : nat -> bv -> bv -> bv **)

  let mul n x y =
    of_N n (N.mul x y)

  (** val uleb : nat -> bv -> bv -> bool **)

  let uleb _ =
    N.leb

  (** val ultb : nat -> bv -> bv -> bool **)

  let ultb _ =
    N.ltb

  (** val sleb : nat -> bv -> bv -> bool **)

  let sleb n x y =
    Z.leb (signed n x) (signed n y)

  (** val sltb : nat -> bv -> bv -> bool **)

  let sltb n x y =
    Z.ltb (signed n x) (signed n y)

  (** val coq_land : nat -> bv -> bv -> bv **)

  let coq_land n x y =
    of_N n (N.coq_land x y)

  (** val coq_lor : nat -> bv -> bv -> bv **)

  let coq_lor n x y =
    of_N n (N.coq_lor x y)

  (** val coq_lxor : nat -> bv -> bv -> bv **)

  let coq_lxor n x y =
    of_N n (N.coq_lxor x y)

  (** val notp : nat -> positive -> coq_N **)

  let rec notp n p =
    match n with
    | O -> N0
    | S n0 ->
      (match p with
       | Coq_xI p0 -> N.double (notp n0 p0)
       | Coq_xO p0 -> N.succ_double (notp n0 p0)
       | Coq_xH -> N.double (onesn n0))

  (** val notn : nat -> coq_N -> coq_N **)

  let notn n = function
  | N0 -> onesn n
  | Npos p -> notp n p

  (** val not : nat -> bv -> bv **)

  let not =
    notn

  module Coq_finite =
   struct
    (** val enumV : (nat -> bool -> 'a1 -> 'a1) -> 'a1 -> nat -> 'a1 list **)

    let rec enumV c n = function
    | O -> Coq_cons (n, Coq_nil)
    | S m0 ->
      Datatypes.app (enumV (fun k -> c (S k)) (c O Coq_false n) m0)
        (enumV (fun k -> c (S k)) (c O Coq_true n) m0)

    (** val enum : nat -> bv list **)

    let enum n =
      enumV cons nil n

    (** val finite_bv : nat -> bv coq_Finite **)

    let finite_bv =
      enum
   end

  module Coq_bitstring =
   struct
    type null =
    | Coq_bN

    type 'a digit =
    | Coq_bO of 'a
    | Coq_bI of 'a
   end

  type bitstring = __

  (** val bitstring_zeroes : nat -> bitstring **)

  let rec bitstring_zeroes = function
  | O -> Obj.magic Coq_bitstring.Coq_bN
  | S n0 -> Obj.magic (Coq_bitstring.Coq_bO (bitstring_zeroes n0))

  (** val fold_left_nat : (nat -> 'a1 -> 'a1) -> 'a1 -> nat -> 'a1 **)

  let rec fold_left_nat s z = function
  | O -> z
  | S n -> fold_left_nat (fun k -> s (S k)) (s O z) n

  (** val fold_left_positive :
      (nat -> 'a1 -> 'a1) -> (nat -> 'a1 -> 'a1) -> 'a1 -> nat -> positive ->
      'a1 **)

  let rec fold_left_positive cI cO n m p =
    match m with
    | O -> n
    | S m0 ->
      (match p with
       | Coq_xI p0 ->
         fold_left_positive (fun k -> cI (S k)) (fun k -> cO (S k)) (cI O n)
           m0 p0
       | Coq_xO p0 ->
         fold_left_positive (fun k -> cI (S k)) (fun k -> cO (S k)) (cO O n)
           m0 p0
       | Coq_xH -> fold_left_nat (fun k -> cO (S k)) (cI O n) m0)

  (** val to_bitstring : nat -> bv -> bitstring **)

  let to_bitstring n = function
  | N0 -> bitstring_zeroes n
  | Npos p ->
    fold_left_positive (fun _ ->
      Obj.magic (fun x0 -> Coq_bitstring.Coq_bI x0)) (fun _ ->
      Obj.magic (fun x0 -> Coq_bitstring.Coq_bO x0))
      (Obj.magic Coq_bitstring.Coq_bN) n p

  (** val fold_bitstring_left :
      (nat -> 'a1 -> bool -> 'a1) -> 'a1 -> nat -> bitstring -> 'a1 **)

  let rec fold_bitstring_left c n m xs =
    match m with
    | O -> n
    | S m0 ->
      (match Obj.magic xs with
       | Coq_bitstring.Coq_bO a ->
         let b = Coq_false in
         fold_bitstring_left (fun k -> c (S k)) (c O n b) m0 a
       | Coq_bitstring.Coq_bI a ->
         let b = Coq_true in
         fold_bitstring_left (fun k -> c (S k)) (c O n b) m0 a)

  (** val of_bitstring : nat -> bitstring -> bv **)

  let of_bitstring =
    fold_bitstring_left (fun k x b -> cons k b x) nil

  (** val seqBv : nat -> bv -> coq_N -> bv list **)

  let seqBv n min len =
    map (of_Z n) (seqZ (unsigned n min) (Z.of_N len))
 end
