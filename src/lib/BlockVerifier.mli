
type __ = Obj.t

type coq_Pred = __

type 'a coq_CPureSpec = __

type 'a coq_CHeapSpec = __

type unit0 =
| Tt

type bool =
| True
| False

type reflect =
| ReflectT
| ReflectF

val negb : bool -> bool

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

val id : __ -> __

type ('a, 'p) sigT =
| ExistT of 'a * 'p

val projT1 : ('a1, 'a2) sigT -> 'a1

val projT2 : ('a1, 'a2) sigT -> 'a2

type sumbool =
| Left
| Right

type uint =
| Nil0
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

val revapp : uint -> uint -> uint

val rev : uint -> uint

module Little :
 sig
  val double : uint -> uint

  val succ_double : uint -> uint
 end

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

val sub : nat -> nat -> nat

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

val internal_eq_rew_r_dep : 'a1 -> 'a1 -> 'a2 -> 'a2

val compose : ('a2 -> 'a3) -> ('a1 -> 'a2) -> 'a1 -> 'a3

val flip : ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a1 -> 'a3

type ('a, 'r) reflexive = 'a -> 'r

type ('a, 'r) transitive = 'a -> 'a -> 'a -> 'r -> 'r -> 'r

type ('a, 'r) preOrder = { preOrder_Reflexive : ('a, 'r) reflexive;
                           preOrder_Transitive : ('a, 'r) transitive }

val bool_dec : bool -> bool -> sumbool

val eqb : bool -> bool -> bool

val iff_reflect : bool -> reflect

module Nat :
 sig
  val add : nat -> nat -> nat

  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool

  val eqb_spec : nat -> nat -> reflect
 end

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val pred_N : positive -> n

  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val div2 : positive -> positive

  val div2_up : positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val eqb : positive -> positive -> bool

  val coq_Nsucc_double : n -> n

  val coq_Ndouble : n -> n

  val coq_lor : positive -> positive -> positive

  val coq_land : positive -> positive -> n

  val ldiff : positive -> positive -> n

  val coq_lxor : positive -> positive -> n

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat

  val of_succ_nat : nat -> positive
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val leb : positive -> positive -> bool

  val of_succ_nat : nat -> positive

  val pow : positive -> positive -> positive

  val shiftl : positive -> n -> positive

  val of_uint_acc : uint -> positive -> positive

  val of_uint : uint -> n

  val to_little_uint : positive -> uint

  val to_uint : positive -> uint

  val eq_dec : positive -> positive -> sumbool
 end

module N :
 sig
  val succ_pos : n -> positive

  val coq_lor : n -> n -> n

  val ldiff : n -> n -> n
 end

module Coq_N :
 sig
  val succ_double : n -> n

  val double : n -> n

  val sub : n -> n -> n

  val compare : n -> n -> comparison

  val leb : n -> n -> bool

  val coq_lor : n -> n -> n

  val coq_land : n -> n -> n

  val coq_lxor : n -> n -> n

  val succ : n -> n

  val add : n -> n -> n

  val mul : n -> n -> n

  val eqb : n -> n -> bool

  val ltb : n -> n -> bool

  val max : n -> n -> n

  val pow : n -> n -> n

  val shiftl : n -> n -> n

  val of_nat : nat -> n

  val of_uint : uint -> n

  val to_uint : n -> uint

  val eq_dec : n -> n -> sumbool
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val pow_pos : z -> positive -> z

  val pow : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val eqb : z -> z -> bool

  val to_nat : z -> nat

  val of_nat : nat -> z

  val of_N : n -> z

  val pos_div_eucl : positive -> z -> (z, z) prod

  val div_eucl : z -> z -> (z, z) prod

  val modulo : z -> z -> z

  val div2 : z -> z

  val shiftl : z -> z -> z

  val shiftr : z -> z -> z

  val coq_land : z -> z -> z

  val to_N : z -> n

  val eq_dec : z -> z -> sumbool
 end

val pow_pos0 : ('a1 -> 'a1 -> 'a1) -> 'a1 -> positive -> 'a1

val pow_N : 'a1 -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> n -> 'a1

val id_phi_N : n -> n

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val seq : nat -> nat -> nat list

val hd : 'a1 -> 'a1 list -> 'a1

val tl : 'a1 list -> 'a1 list

val nth_error : 'a1 list -> nat -> 'a1 option

val rev0 : 'a1 list -> 'a1 list

val rev_append : 'a1 list -> 'a1 list -> 'a1 list

val rev' : 'a1 list -> 'a1 list

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val forallb : ('a1 -> bool) -> 'a1 list -> bool

val find : ('a1 -> bool) -> 'a1 list -> 'a1 option

val jump : positive -> 'a1 list -> 'a1 list

val nth : 'a1 -> positive -> 'a1 list -> 'a1

type 'c pol =
| Pc of 'c
| Pinj of positive * 'c pol
| PX of 'c pol * positive * 'c pol

val p0 : 'a1 -> 'a1 pol

val p1 : 'a1 -> 'a1 pol

val peq : ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol -> bool

val mkPinj : positive -> 'a1 pol -> 'a1 pol

val mkPinj_pred : positive -> 'a1 pol -> 'a1 pol

val mkPX :
  'a1 -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> positive -> 'a1 pol -> 'a1 pol

val mkXi : 'a1 -> 'a1 -> positive -> 'a1 pol

val mkX : 'a1 -> 'a1 -> 'a1 pol

val popp : ('a1 -> 'a1) -> 'a1 pol -> 'a1 pol

val paddC : ('a1 -> 'a1 -> 'a1) -> 'a1 pol -> 'a1 -> 'a1 pol

val psubC : ('a1 -> 'a1 -> 'a1) -> 'a1 pol -> 'a1 -> 'a1 pol

val paddI :
  ('a1 -> 'a1 -> 'a1) -> ('a1 pol -> 'a1 pol -> 'a1 pol) -> 'a1 pol ->
  positive -> 'a1 pol -> 'a1 pol

val psubI :
  ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 pol -> 'a1 pol -> 'a1 pol) ->
  'a1 pol -> positive -> 'a1 pol -> 'a1 pol

val paddX :
  'a1 -> ('a1 -> 'a1 -> bool) -> ('a1 pol -> 'a1 pol -> 'a1 pol) -> 'a1 pol
  -> positive -> 'a1 pol -> 'a1 pol

val psubX :
  'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 pol -> 'a1 pol -> 'a1
  pol) -> 'a1 pol -> positive -> 'a1 pol -> 'a1 pol

val padd :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol ->
  'a1 pol

val psub :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1
  -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol -> 'a1 pol

val pmulC_aux :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 -> 'a1
  pol

val pmulC :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1
  -> 'a1 pol

val pmulI :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 pol ->
  'a1 pol -> 'a1 pol) -> 'a1 pol -> positive -> 'a1 pol -> 'a1 pol

val pmul :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> 'a1 pol -> 'a1 pol -> 'a1 pol

type 'c pExpr =
| PEO
| PEI
| PEc of 'c
| PEX of positive
| PEadd of 'c pExpr * 'c pExpr
| PEsub of 'c pExpr * 'c pExpr
| PEmul of 'c pExpr * 'c pExpr
| PEopp of 'c pExpr
| PEpow of 'c pExpr * n

val mk_X : 'a1 -> 'a1 -> positive -> 'a1 pol

val pEeval :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  'a1) -> ('a1 -> 'a1) -> ('a2 -> 'a1) -> (n -> 'a3) -> ('a1 -> 'a3 -> 'a1)
  -> 'a1 list -> 'a2 pExpr -> 'a1

val ppow_pos :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> ('a1 pol -> 'a1 pol) -> 'a1 pol -> 'a1 pol -> positive -> 'a1 pol

val ppow_N :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> ('a1 pol -> 'a1 pol) -> 'a1 pol -> n -> 'a1 pol

val norm_aux :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pExpr -> 'a1 pol

val mkmult_rec :
  ('a1 -> 'a1 -> positive -> 'a1) -> 'a1 -> ('a1, positive) prod list -> 'a1

val mkmult1 :
  'a1 -> ('a1 -> positive -> 'a1) -> ('a1 -> 'a1 -> positive -> 'a1) -> ('a1,
  positive) prod list -> 'a1

val mkmultm1 :
  'a1 -> ('a1 -> 'a1) -> ('a1 -> positive -> 'a1) -> ('a1 -> 'a1 -> positive
  -> 'a1) -> ('a1, positive) prod list -> 'a1

val mkmult_c_pos :
  'a1 -> 'a2 -> ('a2 -> 'a2 -> bool) -> ('a2 -> 'a1) -> ('a1 -> positive ->
  'a1) -> ('a1 -> 'a1 -> positive -> 'a1) -> 'a2 -> ('a1, positive) prod list
  -> 'a1

val mkmult_c :
  'a1 -> ('a1 -> 'a1) -> 'a2 -> ('a2 -> 'a2 -> bool) -> ('a2 -> 'a1) -> ('a2
  -> 'a2 option) -> ('a1 -> positive -> 'a1) -> ('a1 -> positive -> 'a1) ->
  ('a1 -> 'a1 -> positive -> 'a1) -> 'a2 -> ('a1, positive) prod list -> 'a1

val mkadd_mult :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a2 -> ('a2 -> 'a2 ->
  bool) -> ('a2 -> 'a1) -> ('a2 -> 'a2 option) -> ('a1 -> positive -> 'a1) ->
  ('a1 -> 'a1 -> positive -> 'a1) -> 'a1 -> 'a2 -> ('a1, positive) prod list
  -> 'a1

val add_pow_list :
  'a1 -> n -> ('a1, positive) prod list -> ('a1, positive) prod list

val add_mult_dev :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a2 -> 'a2 ->
  ('a2 -> 'a2 -> bool) -> ('a2 -> 'a1) -> ('a2 -> 'a2 option) -> ('a1 ->
  positive -> 'a1) -> ('a1 -> 'a1 -> positive -> 'a1) -> 'a1 -> 'a2 pol ->
  'a1 list -> n -> ('a1, positive) prod list -> 'a1

val mult_dev :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) ->
  'a2 -> 'a2 -> ('a2 -> 'a2 -> bool) -> ('a2 -> 'a1) -> ('a2 -> 'a2 option)
  -> ('a1 -> positive -> 'a1) -> ('a1 -> positive -> 'a1) -> ('a1 -> 'a1 ->
  positive -> 'a1) -> 'a2 pol -> 'a1 list -> n -> ('a1, positive) prod list
  -> 'a1

val pphi_avoid :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) ->
  'a2 -> 'a2 -> ('a2 -> 'a2 -> bool) -> ('a2 -> 'a1) -> ('a2 -> 'a2 option)
  -> ('a1 -> positive -> 'a1) -> ('a1 -> positive -> 'a1) -> ('a1 -> 'a1 ->
  positive -> 'a1) -> 'a1 list -> 'a2 pol -> 'a1

val mkmult_pow : ('a1 -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> positive -> 'a1

val mkpow : ('a1 -> 'a1 -> 'a1) -> 'a1 -> positive -> 'a1

val mkopp_pow : ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

val pphi_dev :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  'a1) -> ('a1 -> 'a1) -> 'a2 -> 'a2 -> ('a2 -> 'a2 -> bool) -> ('a2 -> 'a1)
  -> ('a2 -> 'a2 option) -> 'a1 list -> 'a2 pol -> 'a1

val get_signZ : z -> z option

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

val ascii_dec : ascii -> ascii -> sumbool

val eqb0 : ascii -> ascii -> bool

type string =
| EmptyString
| String of ascii * string

val string_dec : string -> string -> sumbool

val eqb1 : string -> string -> bool

val append : string -> string -> string

type ('fam, 'signature_index, 'signature) signature =
  'fam -> 'signature_index * 'signature

type 'a noConfusionPackage =
| Build_NoConfusionPackage

type 'a dec_eq = sumbool

type 'a eqDec = 'a -> 'a -> sumbool

val eq_dec0 : 'a1 eqDec -> 'a1 -> 'a1 -> sumbool

type 'a eqDecPoint = 'a -> sumbool

val eq_dec_point : 'a1 -> 'a1 eqDecPoint -> 'a1 -> sumbool

val eqDec_EqDecPoint : 'a1 eqDec -> 'a1 -> 'a1 eqDecPoint

type 'a functionalInduction = { fun_ind_prf : __ }

val uIP_K : 'a1 -> 'a2 -> 'a2

type 'a t =
| Nil1
| Cons0 of 'a * nat * 'a t

val map0 : ('a1 -> 'a2) -> nat -> 'a1 t -> 'a2 t

val unit_eqdec : unit0 -> unit0 -> unit0 dec_eq

val unit_EqDec : unit0 eqDec

val bool_eqdec : bool -> bool -> bool dec_eq

val bool_EqDec : bool eqDec

val nat_eqdec : nat -> nat -> nat dec_eq

val nat_EqDec : nat eqDec

val prod_eqdec : 'a1 eqDec -> 'a2 eqDec -> ('a1, 'a2) prod eqDec

val sum_eqdec : 'a1 eqDec -> 'a2 eqDec -> ('a1, 'a2) sum eqDec

val list_eqdec : 'a1 eqDec -> 'a1 list eqDec

val sigma_eqdec : 'a1 eqDec -> ('a1 -> 'a2 eqDec) -> ('a1, 'a2) sigT eqDec

type decision = sumbool

val decide : decision -> sumbool

type ('a, 'b) relDecision = 'a -> 'b -> decision

val decide_rel : ('a1, 'a2) relDecision -> 'a1 -> 'a2 -> decision

type 'a inhabited = { inhabitant : 'a }

val list_inhabited : 'a1 list inhabited

val bool_inhabated : bool inhabited

val unit_inhabited : unit0 inhabited

val prod_map :
  ('a1 -> 'a2) -> ('a3 -> 'a4) -> ('a1, 'a3) prod -> ('a2, 'a4) prod

val prod_inhabited :
  'a1 inhabited -> 'a2 inhabited -> ('a1, 'a2) prod inhabited

val sum_inhabited_r : 'a2 inhabited -> ('a1, 'a2) sum inhabited

type 'a union = 'a -> 'a -> 'a

val union0 : 'a1 union -> 'a1 -> 'a1 -> 'a1

type 'm fMap = __ -> __ -> (__ -> __) -> 'm -> 'm

val fmap : 'a1 fMap -> ('a2 -> 'a3) -> 'a1 -> 'a1

type ('a, 'm) unionWith = ('a -> 'a -> 'a option) -> 'm -> 'm -> 'm

val union_with :
  ('a1, 'a2) unionWith -> ('a1 -> 'a1 -> 'a1 option) -> 'a2 -> 'a2 -> 'a2

val false_dec : decision

val and_dec : decision -> decision -> decision

val bool_decide : decision -> bool

val option_union_with : ('a1, 'a1 option) unionWith

val option_union : 'a1 option union

module Coq0_N :
 sig
  val lt_dec : (n, n) relDecision
 end

module Coq_Z :
 sig
  val inhabited : z inhabited
 end

val list_fmap : (__ -> __) -> __ list -> __ list

val elem_of_list_dec : ('a1, 'a1) relDecision -> ('a1, 'a1 list) relDecision

val seqZ : z -> z -> z list

module Coq__3 : sig
 type 'a finite = { enum : 'a list }
end
include module type of struct include Coq__3 end

val unit_finite : unit0 finite

type 'a eqbSpecPoint = 'a -> reflect

val f_equal_dec : ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 dec_eq -> 'a2 dec_eq

val f_equal2_dec :
  ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 dec_eq -> 'a2 dec_eq
  -> 'a3 dec_eq

val z_eqdec : z eqDec

val string_eqdec : string eqDec

val eq_dec_het :
  ('a1, 'a2) sigT eqDec -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> ('a1, 'a2) sigT dec_eq

val eqDecision_from_EqDec : 'a1 eqDec -> ('a1, 'a1) relDecision

val finite_sigT :
  'a1 eqDec -> 'a1 finite -> ('a1 -> 'a2 eqDec) -> ('a1 -> 'a2 finite) ->
  ('a1, 'a2) sigT finite

val finite_bool : bool finite

type natComparison =
| EQ of nat
| LT of nat * nat
| GT of nat * nat

val succ_nat_comparison : nat -> nat -> natComparison -> natComparison

val nat_compare : nat -> nat -> natComparison

type 'a isSome = __

val fromSome : 'a1 option -> 'a1 isSome -> 'a1

module Coq_option :
 sig
  val isNone : 'a1 option -> bool

  val map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option

  val bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option

  val traverse_list : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list option
 end

val findAD : 'a1 eqDec -> 'a1 -> ('a1, 'a2) sigT list -> 'a2 option

val find_index_aux : ('a1 -> bool) -> 'a1 list -> nat -> nat option

val find_index : ('a1 -> bool) -> 'a1 list -> nat option

type stats = { branches : n; pruned : n }

val plus_stats : stats -> stats -> stats

module Coq_bv :
 sig
  type bv = { bin : n }

  val bin : nat -> bv -> n

  val eqb : nat -> bv -> bv -> bool

  val eqdec_bv : nat -> bv eqDec

  val trunc : nat -> positive -> n

  val truncn : nat -> n -> n

  val of_N : nat -> n -> bv

  val of_nat : nat -> nat -> bv

  val nil : bv

  val cons : nat -> bool -> bv -> bv

  val bv_case : 'a1 -> (nat -> bool -> bv -> 'a1) -> nat -> bv -> 'a1

  val fold_right : (nat -> bool -> 'a1 -> 'a1) -> 'a1 -> nat -> bv -> 'a1

  val fold_left : (nat -> 'a1 -> bool -> 'a1) -> 'a1 -> nat -> bv -> 'a1

  type coq_NilView =
  | Coq_nvnil

  type coq_ConsView =
  | Coq_cvcons of bool * bv

  val view : nat -> bv -> __

  val app : nat -> nat -> bv -> bv -> bv

  type coq_AppView =
  | Coq_isapp of bv * bv

  val avcons : nat -> nat -> bool -> bv -> coq_AppView -> coq_AppView

  val appView : nat -> nat -> bv -> coq_AppView

  val zero : nat -> bv

  val one : nat -> bv

  val onesp : nat -> positive

  val onesn : nat -> n

  val ones : nat -> bv

  val bv_inhabited : nat -> bv inhabited

  val msbwithcarry : nat -> bool -> bv -> bool

  val msb : nat -> bv -> bool

  val sext' : nat -> bv -> nat -> bv

  val zext' : nat -> bv -> nat -> bv

  type coq_LeView =
  | Coq_is_le of nat

  val leview : nat -> nat -> coq_LeView

  val sext : nat -> bv -> nat -> bv

  val zext : nat -> bv -> nat -> bv

  val truncate : nat -> nat -> bv -> bv

  val unsigned : nat -> bv -> z

  val signed : nat -> bv -> z

  val truncz : nat -> z -> z

  val of_Z : nat -> z -> bv

  val drop : nat -> nat -> bv -> bv

  val take : nat -> nat -> bv -> bv

  val vector_subrange : nat -> nat -> nat -> bv -> bv

  val update_vector_subrange : nat -> nat -> nat -> bv -> bv -> bv

  val shiftr : nat -> nat -> bv -> bv -> bv

  val shiftl : nat -> nat -> bv -> bv -> bv

  val add : nat -> bv -> bv -> bv

  val negate : nat -> bv -> bv

  val sub : nat -> bv -> bv -> bv

  val mul : nat -> bv -> bv -> bv

  val uleb : nat -> bv -> bv -> bool

  val ultb : nat -> bv -> bv -> bool

  val sleb : nat -> bv -> bv -> bool

  val sltb : nat -> bv -> bv -> bool

  val coq_land : nat -> bv -> bv -> bv

  val coq_lor : nat -> bv -> bv -> bv

  val coq_lxor : nat -> bv -> bv -> bv

  val notp : nat -> positive -> n

  val notn : nat -> n -> n

  val not : nat -> bv -> bv

  module Coq_finite :
   sig
    val enumV : (nat -> bool -> 'a1 -> 'a1) -> 'a1 -> nat -> 'a1 list

    val enum : nat -> bv list

    val finite_bv : nat -> bv finite
   end

  module Coq_bitstring :
   sig
    type null =
    | Coq_bN

    type 'a digit =
    | Coq_bO of 'a
    | Coq_bI of 'a
   end

  type bitstring = __

  val bitstring_zeroes : nat -> bitstring

  val fold_left_nat : (nat -> 'a1 -> 'a1) -> 'a1 -> nat -> 'a1

  val fold_left_positive :
    (nat -> 'a1 -> 'a1) -> (nat -> 'a1 -> 'a1) -> 'a1 -> nat -> positive ->
    'a1

  val to_bitstring : nat -> bv -> bitstring

  val fold_bitstring_left :
    (nat -> 'a1 -> bool -> 'a1) -> 'a1 -> nat -> bitstring -> 'a1

  val of_bitstring : nat -> bitstring -> bv

  val seqBv : nat -> bv -> n -> bv list
 end

val uint_of_char : ascii -> uint option -> uint option

module NilEmpty :
 sig
  val string_of_uint : uint -> string

  val uint_of_string : string -> uint option
 end

module Binding :
 sig
  type ('n, 't) coq_Binding = { name : 'n; coq_type : 't }
 end

module Coq_ctx :
 sig
  type 'b coq_Ctx =
  | Coq_nil
  | Coq_snoc of 'b coq_Ctx * 'b

  val coq_Ctx_rect :
    'a2 -> ('a1 coq_Ctx -> 'a2 -> 'a1 -> 'a2) -> 'a1 coq_Ctx -> 'a2

  val coq_NoConfusionPackage_Ctx : 'a1 coq_Ctx noConfusionPackage

  val eq_dec_ctx : 'a1 eqDec -> 'a1 coq_Ctx eqDec

  val cat : 'a1 coq_Ctx -> 'a1 coq_Ctx -> 'a1 coq_Ctx

  type 'b coq_In = { in_at : nat }

  val in_zero : 'a1 -> 'a1 coq_Ctx -> 'a1 coq_In

  val in_succ : 'a1 -> 'a1 coq_Ctx -> 'a1 -> 'a1 coq_In -> 'a1 coq_In

  val coq_In_case :
    ('a1 -> 'a1 coq_Ctx -> 'a2) -> ('a1 -> 'a1 coq_Ctx -> 'a1 -> 'a1 coq_In
    -> 'a2) -> 'a1 -> 'a1 coq_Ctx -> 'a1 coq_In -> 'a2

  val coq_In_rect :
    ('a1 -> 'a1 coq_Ctx -> 'a2) -> ('a1 -> 'a1 coq_Ctx -> 'a1 -> 'a1 coq_In
    -> 'a2 -> 'a2) -> 'a1 -> 'a1 coq_Ctx -> 'a1 coq_In -> 'a2

  type 'b coq_SnocView =
  | Coq_isZero
  | Coq_isSucc of 'b * 'b coq_In

  val view : 'a1 -> 'a1 coq_Ctx -> 'a1 coq_In -> __

  val in_cat_left :
    'a1 -> 'a1 coq_Ctx -> 'a1 coq_Ctx -> 'a1 coq_In -> 'a1 coq_In

  val in_cat_right :
    'a1 -> 'a1 coq_Ctx -> 'a1 coq_Ctx -> 'a1 coq_In -> 'a1 coq_In

  type 'b coq_CatView =
  | Coq_isCatLeft of 'b coq_In
  | Coq_isCatRight of 'b coq_In

  val catView :
    'a1 coq_Ctx -> 'a1 coq_Ctx -> 'a1 -> 'a1 coq_In -> 'a1 coq_CatView

  val coq_In_eqb :
    'a1 coq_Ctx -> 'a1 -> 'a1 -> 'a1 coq_In -> 'a1 coq_In -> bool

  val coq_In_eqb_spec :
    'a1 coq_Ctx -> 'a1 -> 'a1 -> 'a1 coq_In -> 'a1 coq_In -> reflect

  type ('b, 'p) coq_All =
  | Coq_all_nil
  | Coq_all_snoc of 'b coq_Ctx * 'b * ('b, 'p) coq_All * 'p

  val all_intro : ('a1 -> 'a2) -> 'a1 coq_Ctx -> ('a1, 'a2) coq_All

  val remove : 'a1 coq_Ctx -> 'a1 -> 'a1 coq_In -> 'a1 coq_Ctx

  val shift_var :
    'a1 -> 'a1 -> 'a1 coq_Ctx -> 'a1 coq_In -> 'a1 coq_In -> 'a1 coq_In

  type 'b coq_OccursCheckView =
  | Same
  | Diff of 'b * 'b coq_In

  val occurs_check_view_step :
    'a1 coq_Ctx -> 'a1 -> 'a1 -> 'a1 -> 'a1 coq_In -> 'a1 coq_In -> 'a1
    coq_OccursCheckView -> 'a1 coq_OccursCheckView

  val occurs_check_view :
    'a1 coq_Ctx -> 'a1 -> 'a1 coq_In -> 'a1 -> 'a1 coq_In -> 'a1
    coq_OccursCheckView

  val forallb : 'a1 coq_Ctx -> ('a1 -> 'a1 coq_In -> bool) -> bool

  val map : ('a1 -> 'a2) -> 'a1 coq_Ctx -> 'a2 coq_Ctx

  val in_map : ('a1 -> 'a2) -> 'a1 -> 'a1 coq_Ctx -> 'a1 coq_In -> 'a2 coq_In

  val resolve :
    'a1 eqDec -> ('a1, 'a2) Binding.coq_Binding coq_Ctx -> 'a1 -> 'a2 option

  val resolve_mk_in :
    'a1 eqDec -> ('a1, 'a2) Binding.coq_Binding coq_Ctx -> 'a1 -> 'a2 isSome
    -> ('a1, 'a2) Binding.coq_Binding coq_In

  val names : ('a1, 'a2) Binding.coq_Binding coq_Ctx -> 'a1 list

  val split_at_dot' : string -> (string -> string -> 'a1) -> 'a1

  val split_at_dot : string -> (string, string) prod

  val parse_number : string -> n

  val unparse_number : n -> string

  val max_with_base : string -> string list -> n

  val fresh :
    (string, 'a1) Binding.coq_Binding coq_Ctx -> string option -> string
 end

module Coq_env :
 sig
  type ('b, 'd) coq_Env =
  | Coq_nil
  | Coq_snoc of 'b Coq_ctx.coq_Ctx * ('b, 'd) coq_Env * 'b * 'd

  val coq_Env_rect :
    'a3 -> ('a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> 'a3 -> 'a1 -> 'a2 ->
    'a3) -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> 'a3

  type ('b, 'd) coq_NilView =
  | Coq_isNil

  type ('b, 'd) coq_SnocView =
  | Coq_isSnoc of ('b, 'd) coq_Env * 'd

  val view : 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> __

  val cat :
    'a1 Coq_ctx.coq_Ctx -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> ('a1,
    'a2) coq_Env -> ('a1, 'a2) coq_Env

  type ('b, 'd) coq_CatView =
  | Coq_isCat of ('b, 'd) coq_Env * ('b, 'd) coq_Env

  val catView :
    'a1 Coq_ctx.coq_Ctx -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> ('a1,
    'a2) coq_CatView

  val coq_NoConfusionPackage_Env :
    ('a1 Coq_ctx.coq_Ctx * ('a1, 'a2) coq_Env) noConfusionPackage

  val lookup :
    'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> 'a1 -> 'a1 Coq_ctx.coq_In ->
    'a2

  type ('b, 'd, 'q) coq_All =
  | Coq_all_nil
  | Coq_all_snoc of 'b Coq_ctx.coq_Ctx * ('b, 'd) coq_Env * 'b * 'd
     * ('b, 'd, 'q) coq_All * 'q

  val all_snoc_inv_1 :
    'a1 Coq_ctx.coq_Ctx -> 'a1 -> ('a1, 'a2) coq_Env -> 'a2 -> ('a1, 'a2,
    'a3) coq_All -> ('a1, 'a2, 'a3) coq_All

  val all_snoc_inv_2 :
    'a1 Coq_ctx.coq_Ctx -> 'a1 -> ('a1, 'a2) coq_Env -> 'a2 -> ('a1, 'a2,
    'a3) coq_All -> 'a3

  val all_intro :
    ('a1 -> 'a2 -> 'a3) -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> ('a1,
    'a2, 'a3) coq_All

  val eqb_hom :
    ('a1 -> 'a2 -> 'a2 -> bool) -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env
    -> ('a1, 'a2) coq_Env -> bool

  val eqb_hom_spec_point :
    ('a1 -> 'a2 -> 'a2 -> bool) -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env
    -> ('a1, 'a2, 'a2 eqbSpecPoint) coq_All -> ('a1, 'a2) coq_Env eqbSpecPoint

  val eqb_hom_spec :
    ('a1 -> 'a2 -> 'a2 -> bool) -> ('a1 -> 'a2 -> 'a2 -> reflect) -> 'a1
    Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> ('a1, 'a2) coq_Env -> reflect

  val tabulate :
    'a1 Coq_ctx.coq_Ctx -> ('a1 -> 'a1 Coq_ctx.coq_In -> 'a2) -> ('a1, 'a2)
    coq_Env

  val update :
    'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> 'a1 -> 'a1 Coq_ctx.coq_In ->
    'a2 -> ('a1, 'a2) coq_Env

  val head : 'a1 Coq_ctx.coq_Ctx -> 'a1 -> ('a1, 'a2) coq_Env -> 'a2

  val tail :
    'a1 Coq_ctx.coq_Ctx -> 'a1 -> ('a1, 'a2) coq_Env -> ('a1, 'a2) coq_Env

  val drop :
    'a1 Coq_ctx.coq_Ctx -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> ('a1,
    'a2) coq_Env

  val remove :
    'a1 Coq_ctx.coq_Ctx -> 'a1 -> ('a1, 'a2) coq_Env -> 'a1 Coq_ctx.coq_In ->
    ('a1, 'a2) coq_Env

  type ('b, 'd, 'r) abstract = __

  val kvsnoc :
    'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> ('a1, 'a2) sigT -> ('a1,
    'a2) coq_Env

  val map :
    ('a1 -> 'a2 -> 'a3) -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Env -> ('a1,
    'a3) coq_Env
 end

module Coq_envrec :
 sig
  type ('b, 'd) coq_EnvRec = __

  val to_env :
    'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_EnvRec -> ('a1, 'a2) Coq_env.coq_Env

  val of_env :
    'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2) Coq_env.coq_Env -> ('a1, 'a2) coq_EnvRec
 end

type ('x, 't, 'd) namedEnv =
  (('x, 't) Binding.coq_Binding, 'd) Coq_env.coq_Env

type ('x, 't, 'd, 'r) abstract_named =
  (('x, 't) Binding.coq_Binding, 'd, 'r) Coq_env.abstract

type varKit = { pVar_eq_dec : __ eqDec; lVar_eq_dec : __ eqDec;
                pVartoLVar : (__ -> __);
                fresh_pvar : (__ -> (__, __) Binding.coq_Binding
                             Coq_ctx.coq_Ctx -> __ option -> __);
                fresh_lvar : (__ -> (__, __) Binding.coq_Binding
                             Coq_ctx.coq_Ctx -> __ option -> __) }

type pVar = __

type lVar = __

val fresh_lvar :
  varKit -> (lVar, 'a1) Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar option ->
  lVar

val defaultVarKit : varKit

module Coq_ty :
 sig
  type coq_TypeDeclKit =
  | Build_TypeDeclKit

  type enumi = __

  type unioni = __

  type recordi = __

  type coq_Ty =
  | Coq_int
  | Coq_bool
  | Coq_string
  | Coq_list of coq_Ty
  | Coq_prod of coq_Ty * coq_Ty
  | Coq_sum of coq_Ty * coq_Ty
  | Coq_unit
  | Coq_enum of enumi
  | Coq_bvec of nat
  | Coq_tuple of coq_Ty Coq_ctx.coq_Ctx
  | Coq_union of unioni
  | Coq_record of recordi

  val coq_NoConfusionPackage_Ty : coq_TypeDeclKit -> coq_Ty noConfusionPackage

  val option : coq_TypeDeclKit -> coq_Ty -> coq_Ty

  val coq_Ty_rect :
    coq_TypeDeclKit -> 'a1 -> 'a1 -> 'a1 -> (coq_Ty -> 'a1 -> 'a1) -> (coq_Ty
    -> coq_Ty -> 'a1 -> 'a1 -> 'a1) -> (coq_Ty -> coq_Ty -> 'a1 -> 'a1 ->
    'a1) -> 'a1 -> (enumi -> 'a1) -> (nat -> 'a1) -> (coq_Ty Coq_ctx.coq_Ctx
    -> (coq_Ty, 'a1) Coq_ctx.coq_All -> 'a1) -> (unioni -> 'a1) -> (recordi
    -> 'a1) -> coq_Ty -> 'a1

  val coq_Ty_rec :
    coq_TypeDeclKit -> 'a1 -> 'a1 -> 'a1 -> (coq_Ty -> 'a1 -> 'a1) -> (coq_Ty
    -> coq_Ty -> 'a1 -> 'a1 -> 'a1) -> (coq_Ty -> coq_Ty -> 'a1 -> 'a1 ->
    'a1) -> 'a1 -> (enumi -> 'a1) -> (nat -> 'a1) -> (coq_Ty Coq_ctx.coq_Ctx
    -> (coq_Ty, 'a1) Coq_ctx.coq_All -> 'a1) -> (unioni -> 'a1) -> (recordi
    -> 'a1) -> coq_Ty -> 'a1

  type coq_TypeDenoteKit =
  | Build_TypeDenoteKit

  type enumt = __

  type uniont = __

  type recordt = __

  type coq_Val = __

  type coq_TypeDefKit = { enum_eqdec : enumi eqDec;
                          union_eqdec : unioni eqDec;
                          record_eqdec : recordi eqDec;
                          enumt_eqdec : (enumi -> enumt eqDec);
                          enumt_finite : (enumi -> enumt finite);
                          uniont_eqdec : (unioni -> uniont eqDec);
                          unionk_eqdec : (unioni -> __ eqDec);
                          unionk_finite : (unioni -> __ finite);
                          unionk_ty : (unioni -> __ -> coq_Ty);
                          recordt_eqdec : (recordi -> recordt eqDec);
                          recordf_ty : (recordi -> (__, coq_Ty)
                                       Binding.coq_Binding Coq_ctx.coq_Ctx);
                          unionv_fold : (unioni -> (__, coq_Val) sigT ->
                                        uniont);
                          unionv_unfold : (unioni -> uniont -> (__, coq_Val)
                                          sigT);
                          recordv_fold : (recordi -> (__, coq_Ty, coq_Val)
                                         namedEnv -> recordt);
                          recordv_unfold : (recordi -> recordt -> (__,
                                           coq_Ty, coq_Val) namedEnv) }

  val enum_eqdec :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> enumi eqDec

  val union_eqdec :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> unioni eqDec

  val record_eqdec :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> recordi eqDec

  val enumt_eqdec :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> enumi -> enumt
    eqDec

  val enumt_finite :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> enumi -> enumt
    finite

  val uniont_eqdec :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> unioni ->
    uniont eqDec

  type unionk = __

  val unionk_eqdec :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> unioni ->
    unionk eqDec

  val unionk_finite :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> unioni ->
    unionk finite

  val unionk_ty :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> unioni ->
    unionk -> coq_Ty

  val recordt_eqdec :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> recordi ->
    recordt eqDec

  type recordf = __

  val recordf_ty :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> recordi ->
    (recordf, coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  val unionv_fold :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> unioni ->
    (unionk, coq_Val) sigT -> uniont

  val unionv_unfold :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> unioni ->
    uniont -> (unionk, coq_Val) sigT

  val recordv_fold :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> recordi ->
    (recordf, coq_Ty, coq_Val) namedEnv -> recordt

  val recordv_unfold :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> recordi ->
    recordt -> (recordf, coq_Ty, coq_Val) namedEnv

  val coq_Ty_eq_dec :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> coq_Ty eqDec

  val coq_Val_eq_dec :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_TypeDefKit -> coq_Ty ->
    coq_Val eqDec

  val inhabit :
    coq_TypeDeclKit -> coq_TypeDenoteKit -> coq_Ty -> coq_Val option
 end

module Coq_bop :
 sig
  type coq_RelOp =
  | Coq_eq of Coq_ty.coq_Ty
  | Coq_neq of Coq_ty.coq_Ty
  | Coq_le
  | Coq_lt
  | Coq_bvsle of nat
  | Coq_bvslt of nat
  | Coq_bvule of nat
  | Coq_bvult of nat

  type coq_BinOp =
  | Coq_plus
  | Coq_minus
  | Coq_times
  | Coq_land
  | Coq_and
  | Coq_or
  | Coq_pair of Coq_ty.coq_Ty * Coq_ty.coq_Ty
  | Coq_cons of Coq_ty.coq_Ty
  | Coq_append of Coq_ty.coq_Ty
  | Coq_shiftr of nat * nat
  | Coq_shiftl of nat * nat
  | Coq_bvadd of nat
  | Coq_bvsub of nat
  | Coq_bvmul of nat
  | Coq_bvand of nat
  | Coq_bvor of nat
  | Coq_bvxor of nat
  | Coq_bvapp of nat * nat
  | Coq_bvcons of nat
  | Coq_update_vector_subrange of nat * nat * nat
  | Coq_relop of Coq_ty.coq_Ty * coq_RelOp

  type coq_BinOp_sig = coq_BinOp

  type coq_RelOp_sig = coq_RelOp

  val coq_RelOp_eqdec :
    Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_Ty -> coq_RelOp -> coq_RelOp ->
    coq_RelOp dec_eq

  val coq_RelOp_EqDec :
    Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_Ty -> coq_RelOp eqDec

  type coq_RelOpTel = Coq_ty.coq_Ty * coq_RelOp_sig

  type coq_BinOpTel =
    (Coq_ty.coq_Ty * (Coq_ty.coq_Ty * Coq_ty.coq_Ty)) * coq_BinOp_sig

  val binoptel_pair :
    Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_BinOpTel

  val binoptel_cons : Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_Ty -> coq_BinOpTel

  val binoptel_append :
    Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_Ty -> coq_BinOpTel

  val binoptel_shiftr : Coq_ty.coq_TypeDeclKit -> nat -> nat -> coq_BinOpTel

  val binoptel_shiftl : Coq_ty.coq_TypeDeclKit -> nat -> nat -> coq_BinOpTel

  val reloptel_eq_dec :
    Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_TypeDenoteKit ->
    Coq_ty.coq_TypeDefKit -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_RelOp ->
    coq_RelOp -> coq_RelOpTel dec_eq

  val binoptel_eq_dec_relop :
    Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_TypeDenoteKit ->
    Coq_ty.coq_TypeDefKit -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_RelOp ->
    coq_RelOp -> coq_BinOpTel dec_eq

  val update_vector_subrange_eq_dec_clause_1_clause_1_clause_1 :
    Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> nat -> nat -> sumbool
    -> nat -> nat -> sumbool -> coq_BinOpTel dec_eq

  val update_vector_subrange_eq_dec_clause_1_clause_1 :
    Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> nat -> nat -> sumbool
    -> nat -> nat -> coq_BinOpTel dec_eq

  val update_vector_subrange_eq_dec_clause_1 :
    Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> nat -> nat -> nat ->
    nat -> coq_BinOpTel dec_eq

  val update_vector_subrange_eq_dec :
    Coq_ty.coq_TypeDeclKit -> nat -> nat -> nat -> nat -> nat -> nat ->
    coq_BinOpTel dec_eq

  val binoptel_eq_dec :
    Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_TypeDenoteKit ->
    Coq_ty.coq_TypeDefKit -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_BinOp ->
    coq_BinOp -> coq_BinOpTel dec_eq

  val eqdep_dec :
    Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_TypeDenoteKit ->
    Coq_ty.coq_TypeDefKit -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_BinOp ->
    coq_BinOp -> sumbool

  val eval_relop_val :
    Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_TypeDenoteKit ->
    Coq_ty.coq_TypeDefKit -> Coq_ty.coq_Ty -> coq_RelOp -> Coq_ty.coq_Val ->
    Coq_ty.coq_Val -> bool

  val eval :
    Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_TypeDenoteKit ->
    Coq_ty.coq_TypeDefKit -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty
    -> coq_BinOp -> Coq_ty.coq_Val -> Coq_ty.coq_Val -> Coq_ty.coq_Val
 end

module Coq_uop :
 sig
  type coq_UnOp =
  | Coq_inl of Coq_ty.coq_Ty * Coq_ty.coq_Ty
  | Coq_inr of Coq_ty.coq_Ty * Coq_ty.coq_Ty
  | Coq_neg
  | Coq_not
  | Coq_rev of Coq_ty.coq_Ty
  | Coq_sext of nat * nat
  | Coq_zext of nat * nat
  | Coq_get_slice_int of nat
  | Coq_signed of nat
  | Coq_unsigned of nat
  | Coq_truncate of nat * nat
  | Coq_vector_subrange of nat * nat * nat
  | Coq_bvnot of nat
  | Coq_bvdrop of nat * nat
  | Coq_bvtake of nat * nat
  | Coq_negate of nat

  type coq_Tel = Coq_ty.coq_Ty * coq_UnOp

  val tel_eq_dec_clause_6 :
    Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> nat -> coq_Tel dec_eq

  val tel_eq_dec_clause_7 :
    Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> nat -> coq_Tel dec_eq

  val tel_eq_dec_clause_10 :
    Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> coq_Tel dec_eq

  val tel_eq_dec_clause_9 :
    Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> coq_Tel dec_eq

  val tel_eq_dec_clause_11 :
    Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> nat -> coq_Tel dec_eq

  val tel_eq_dec_clause_12_clause_1 :
    Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> nat -> nat -> nat ->
    sumbool -> coq_Tel dec_eq

  val tel_eq_dec_clause_12 :
    Coq_ty.coq_TypeDeclKit -> nat -> nat -> sumbool -> nat -> nat -> nat ->
    coq_Tel dec_eq

  val tel_eq_dec_clause_14 :
    Coq_ty.coq_TypeDeclKit -> nat -> nat -> nat -> sumbool -> coq_Tel dec_eq

  val tel_eq_dec_clause_15 :
    Coq_ty.coq_TypeDeclKit -> nat -> nat -> nat -> sumbool -> coq_Tel dec_eq

  val tel_eq_dec :
    Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty
    -> coq_UnOp -> coq_UnOp -> coq_Tel dec_eq

  val eval :
    Coq_ty.coq_TypeDeclKit -> Coq_ty.coq_TypeDenoteKit -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> coq_UnOp -> Coq_ty.coq_Val -> Coq_ty.coq_Val
 end

val iffP : bool -> reflect -> reflect

val plusNatPos : nat -> positive -> positive

module type Base =
 sig
  val typedeclkit : Coq_ty.coq_TypeDeclKit

  val typedenotekit : Coq_ty.coq_TypeDenoteKit

  val typedefkit : Coq_ty.coq_TypeDefKit

  val varkit : varKit

  type _UU1d479__UU1d46c__UU1d46e_

  val _UU1d479__UU1d46c__UU1d46e__eq_dec :
    (Coq_ty.coq_Ty, _UU1d479__UU1d46c__UU1d46e_) sigT eqDec

  val _UU1d479__UU1d46c__UU1d46e__finite :
    (Coq_ty.coq_Ty, _UU1d479__UU1d46c__UU1d46e_) sigT finite

  type coq_Memory

  type coq_Exp =
  | Coq_exp_var of pVar * Coq_ty.coq_Ty
     * (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_exp_val of Coq_ty.coq_Ty * Coq_ty.coq_Val
  | Coq_exp_binop of Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Exp * coq_Exp
  | Coq_exp_unop of Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Exp
  | Coq_exp_list of Coq_ty.coq_Ty * coq_Exp list
  | Coq_exp_bvec of nat * coq_Exp t
  | Coq_exp_tuple of Coq_ty.coq_Ty Coq_ctx.coq_Ctx
     * (Coq_ty.coq_Ty, coq_Exp) Coq_env.coq_Env
  | Coq_exp_union of Coq_ty.unioni * Coq_ty.unionk * coq_Exp
  | Coq_exp_record of Coq_ty.recordi
     * (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Exp) namedEnv

  val coq_Exp_rect :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar ->
    Coq_ty.coq_Ty -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Val -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Exp -> 'a1 ->
    coq_Exp -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Exp -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty -> coq_Exp
    list -> __ -> 'a1) -> (nat -> coq_Exp t -> __ -> 'a1) -> (Coq_ty.coq_Ty
    Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, coq_Exp) Coq_env.coq_Env -> __ -> 'a1)
    -> (Coq_ty.unioni -> Coq_ty.unionk -> coq_Exp -> 'a1 -> 'a1) ->
    (Coq_ty.recordi -> (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Exp) namedEnv ->
    __ -> 'a1) -> Coq_ty.coq_Ty -> coq_Exp -> 'a1

  val coq_Exp_rec :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar ->
    Coq_ty.coq_Ty -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Val -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Exp -> 'a1 ->
    coq_Exp -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Exp -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty -> coq_Exp
    list -> __ -> 'a1) -> (nat -> coq_Exp t -> __ -> 'a1) -> (Coq_ty.coq_Ty
    Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, coq_Exp) Coq_env.coq_Env -> __ -> 'a1)
    -> (Coq_ty.unioni -> Coq_ty.unionk -> coq_Exp -> 'a1 -> 'a1) ->
    (Coq_ty.recordi -> (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Exp) namedEnv ->
    __ -> 'a1) -> Coq_ty.coq_Ty -> coq_Exp -> 'a1

  val eval :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Exp -> (pVar, Coq_ty.coq_Ty, Coq_ty.coq_Val)
    namedEnv -> Coq_ty.coq_Val

  val evals :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
    Coq_ty.coq_Ty, coq_Exp) namedEnv -> (pVar, Coq_ty.coq_Ty, Coq_ty.coq_Val)
    namedEnv -> (pVar, Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv

  val exp_truncate :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> coq_Exp -> coq_Exp

  val exp_vector_subrange :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> nat -> coq_Exp -> coq_Exp

  val exp_update_vector_subrange :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> nat -> coq_Exp -> coq_Exp -> coq_Exp

  type coq_Term =
  | Coq_term_var of lVar * Coq_ty.coq_Ty
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_term_val of Coq_ty.coq_Ty * Coq_ty.coq_Val
  | Coq_term_binop of Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_term_unop of Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term
  | Coq_term_tuple of Coq_ty.coq_Ty Coq_ctx.coq_Ctx
     * (Coq_ty.coq_Ty, coq_Term) Coq_env.coq_Env
  | Coq_term_union of Coq_ty.unioni * Coq_ty.unionk * coq_Term
  | Coq_term_record of Coq_ty.recordi
     * (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Term) namedEnv

  val coq_NoConfusionPackage_Term :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (Coq_ty.coq_Ty * coq_Term) noConfusionPackage

  type coq_Term_sig = coq_Term

  val coq_Term_sig_pack :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> Coq_ty.coq_Ty * coq_Term

  val coq_Term_Signature :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> (coq_Term, Coq_ty.coq_Ty, coq_Term_sig) signature

  val term_enum :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.enumi
    -> Coq_ty.enumt -> coq_Term

  val term_list :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term list -> coq_Term

  val term_bvec :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term t -> coq_Term

  val term_relop_neg :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> coq_Term -> coq_Term -> coq_Term

  val term_truncate :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> coq_Term -> coq_Term

  val term_vector_subrange :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> nat -> coq_Term -> coq_Term

  val term_update_vector_subrange :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> nat -> coq_Term -> coq_Term -> coq_Term

  val coq_Term_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar ->
    Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Val -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1 -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty
    Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, coq_Term) Coq_env.coq_Env ->
    (Coq_ty.coq_Ty, coq_Term, 'a1) Coq_env.coq_All -> 'a1) -> (Coq_ty.unioni
    -> Coq_ty.unionk -> coq_Term -> 'a1 -> 'a1) -> (Coq_ty.recordi ->
    (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Term) namedEnv -> ((Coq_ty.recordf,
    Coq_ty.coq_Ty) Binding.coq_Binding, coq_Term, 'a1) Coq_env.coq_All ->
    'a1) -> Coq_ty.coq_Ty -> coq_Term -> 'a1

  val coq_Term_rec :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar ->
    Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Val -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1 -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty
    Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, coq_Term) Coq_env.coq_Env ->
    (Coq_ty.coq_Ty, coq_Term, 'a1) Coq_env.coq_All -> 'a1) -> (Coq_ty.unioni
    -> Coq_ty.unionk -> coq_Term -> 'a1 -> 'a1) -> (Coq_ty.recordi ->
    (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Term) namedEnv -> ((Coq_ty.recordf,
    Coq_ty.coq_Ty) Binding.coq_Binding, coq_Term, 'a1) Coq_env.coq_All ->
    'a1) -> Coq_ty.coq_Ty -> coq_Term -> 'a1

  val coq_Term_int_case :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (Coq_ty.coq_Val -> 'a1) -> (coq_Term -> coq_Term -> 'a1) -> (coq_Term ->
    coq_Term -> 'a1) -> (coq_Term -> coq_Term -> 'a1) -> (coq_Term ->
    coq_Term -> 'a1) -> (coq_Term -> 'a1) -> (nat -> coq_Term -> 'a1) -> (nat
    -> coq_Term -> 'a1) -> coq_Term -> 'a1

  val coq_Term_int_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (Coq_ty.coq_Val -> 'a1) -> (coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) ->
    (coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) -> (coq_Term -> coq_Term ->
    'a1 -> 'a1 -> 'a1) -> (coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) ->
    (coq_Term -> 'a1 -> 'a1) -> (nat -> coq_Term -> 'a1) -> (nat -> coq_Term
    -> 'a1) -> coq_Term -> 'a1

  val coq_Term_bool_case :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (Coq_ty.coq_Val -> 'a1) -> (coq_Term -> coq_Term -> 'a1) -> (coq_Term ->
    coq_Term -> 'a1) -> (Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> coq_Term ->
    coq_Term -> 'a1) -> (coq_Term -> 'a1) -> coq_Term -> 'a1

  val coq_Term_bool_ind :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (Coq_ty.coq_Val -> 'a1) -> (coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) ->
    (coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_bop.coq_RelOp -> coq_Term -> coq_Term -> 'a1) -> (coq_Term -> 'a1 ->
    'a1) -> coq_Term -> 'a1

  val coq_Term_list_case :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> (lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) -> (coq_Term ->
    coq_Term -> 'a1) -> (coq_Term -> coq_Term -> 'a1) -> (coq_Term -> 'a1) ->
    coq_Term -> 'a1

  val coq_Term_prod_case :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> (lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) ->
    (coq_Term -> coq_Term -> 'a1) -> coq_Term -> 'a1

  val coq_Term_sum_case :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> (lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) ->
    (coq_Term -> 'a1) -> (coq_Term -> 'a1) -> coq_Term -> 'a1

  val coq_Term_bvec_case :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (nat -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term
    -> coq_Term -> 'a1) -> (nat -> nat -> nat -> __ -> coq_Term -> coq_Term
    -> 'a1) -> (nat -> coq_Term -> 'a1) -> (nat -> coq_Term -> 'a1) -> (nat
    -> nat -> __ -> coq_Term -> 'a1) -> (nat -> nat -> __ -> coq_Term -> 'a1)
    -> (nat -> coq_Term -> 'a1) -> (nat -> nat -> __ -> coq_Term -> 'a1) ->
    (nat -> nat -> nat -> __ -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term
    -> 'a1) -> (nat -> nat -> coq_Term -> 'a1) -> nat -> coq_Term -> 'a1

  val coq_Term_bvec_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (nat -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1 ->
    'a1 -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) -> (nat
    -> coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> 'a1 -> 'a1 -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1 ->
    'a1 -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) -> (nat
    -> nat -> coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) -> (nat -> nat -> coq_Term ->
    coq_Term -> 'a1 -> 'a1 -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1 ->
    'a1) -> (nat -> nat -> nat -> __ -> coq_Term -> coq_Term -> 'a1 -> 'a1 ->
    'a1) -> (nat -> coq_Term -> 'a1 -> 'a1) -> (nat -> coq_Term -> 'a1 ->
    'a1) -> (nat -> nat -> __ -> coq_Term -> 'a1 -> 'a1) -> (nat -> nat -> __
    -> coq_Term -> 'a1 -> 'a1) -> (nat -> coq_Term -> 'a1) -> (nat -> nat ->
    __ -> coq_Term -> 'a1 -> 'a1) -> (nat -> nat -> nat -> __ -> coq_Term ->
    'a1 -> 'a1) -> (nat -> nat -> coq_Term -> 'a1 -> 'a1) -> (nat -> nat ->
    coq_Term -> 'a1 -> 'a1) -> nat -> coq_Term -> 'a1

  val coq_Term_tuple_case :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) ->
    ((Coq_ty.coq_Ty, coq_Term) Coq_env.coq_Env -> 'a1) -> coq_Term -> 'a1

  val coq_Term_union_case :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.unioni -> (lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) -> (Coq_ty.unionk ->
    coq_Term -> 'a1) -> coq_Term -> 'a1

  val coq_Term_record_case :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.recordi -> (lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) -> ((Coq_ty.recordf,
    Coq_ty.coq_Ty, coq_Term) namedEnv -> 'a1) -> coq_Term -> 'a1

  type coq_ListView =
  | Coq_term_list_var of lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_term_list_val of Coq_ty.coq_Val
  | Coq_term_list_cons of coq_Term * coq_Term * coq_ListView
  | Coq_term_list_append of coq_Term * coq_Term * coq_ListView * coq_ListView
  | Coq_term_list_rev of coq_Term * coq_ListView

  val coq_ListView_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> (lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) -> (coq_Term ->
    coq_Term -> coq_ListView -> 'a1 -> 'a1) -> (coq_Term -> coq_Term ->
    coq_ListView -> 'a1 -> coq_ListView -> 'a1 -> 'a1) -> (coq_Term ->
    coq_ListView -> 'a1 -> 'a1) -> coq_Term -> coq_ListView -> 'a1

  val coq_ListView_rec :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> (lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) -> (coq_Term ->
    coq_Term -> coq_ListView -> 'a1 -> 'a1) -> (coq_Term -> coq_Term ->
    coq_ListView -> 'a1 -> coq_ListView -> 'a1 -> 'a1) -> (coq_Term ->
    coq_ListView -> 'a1 -> 'a1) -> coq_Term -> coq_ListView -> 'a1

  type coq_View = __

  val view_var :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar ->
    Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> coq_View

  val view_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Val -> coq_View

  val view_binop :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> coq_View -> coq_View -> coq_View

  val view_unop :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    coq_View -> coq_View

  val view :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> coq_View

  val coq_Term_eqb_clause_3 :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (Coq_ty.coq_Ty -> coq_Term -> coq_Term -> bool) -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    sumbool -> coq_Term -> coq_Term -> bool

  val coq_Term_eqb_clause_4 :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (Coq_ty.coq_Ty -> coq_Term -> coq_Term -> bool) -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> sumbool -> coq_Term -> bool

  val coq_Term_eqb_clause_6 :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (Coq_ty.coq_Ty -> coq_Term -> coq_Term -> bool) -> Coq_ty.unioni ->
    Coq_ty.unionk -> coq_Term -> Coq_ty.unionk -> sumbool -> coq_Term -> bool

  val coq_Term_eqb :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> coq_Term -> bool

  val coq_Term_eqb_spec :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> coq_Term -> reflect

  type 'a coq_List = 'a list

  type 'a coq_Const = 'a

  type coq_Sub =
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding, coq_Term) Coq_env.coq_Env

  type 't coq_Subst =
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 't -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub -> 't

  val subst :
    'a1 coq_Subst -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_Sub -> 'a1

  val sub_term :
    Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_Term -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_Sub -> coq_Term

  val coq_SubstTerm : Coq_ty.coq_Ty -> coq_Term coq_Subst

  val coq_SubstList : 'a1 coq_Subst -> 'a1 coq_List coq_Subst

  val coq_SubstConst : 'a1 coq_Const coq_Subst

  val coq_SubstEnv :
    ('a1 -> 'a2 coq_Subst) -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2)
    Coq_env.coq_Env coq_Subst

  val sub_id :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub

  val sub_snoc :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_Term -> coq_Sub

  val sub_shift :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_Sub

  val sub_wk1 :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_Sub

  val sub_cat_left :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub

  val sub_cat_right :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub

  val sub_up1 :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_Sub

  val sub_up :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub

  val sub_single :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_Term -> coq_Sub

  type 't coq_SubstLaws =
  | Build_SubstLaws

  val coq_SubstLawsTerm : Coq_ty.coq_Ty -> coq_Term coq_SubstLaws

  val coq_SubstLawsList :
    'a1 coq_Subst -> 'a1 coq_SubstLaws -> 'a1 coq_List coq_SubstLaws

  val coq_SubstLawsConst : 'a1 coq_Const coq_SubstLaws

  val coq_SubstLawsEnv :
    ('a1 -> 'a2 coq_Subst) -> ('a1 -> 'a2 coq_SubstLaws) -> 'a1
    Coq_ctx.coq_Ctx -> ('a1, 'a2) Coq_env.coq_Env coq_SubstLaws

  val subst_ctx : 'a1 coq_Subst -> 'a1 Coq_ctx.coq_Ctx coq_Subst

  val substlaws_ctx :
    'a1 coq_Subst -> 'a1 coq_SubstLaws -> 'a1 Coq_ctx.coq_Ctx coq_SubstLaws

  module SubNotations :
   sig
   end

  type ('a, 'b) coq_Pair = ('a, 'b) prod

  val coq_SubstPair :
    'a1 coq_Subst -> 'a2 coq_Subst -> ('a1, 'a2) coq_Pair coq_Subst

  val coq_SubstLawsPair :
    'a1 coq_Subst -> 'a1 coq_SubstLaws -> 'a2 coq_Subst -> 'a2 coq_SubstLaws
    -> ('a1, 'a2) coq_Pair coq_SubstLaws

  type 'a coq_Option = 'a option

  val coq_SubstOption : 'a1 coq_Subst -> 'a1 coq_Option coq_Subst

  val coq_SubstLawsOption :
    'a1 coq_Subst -> 'a1 coq_SubstLaws -> 'a1 coq_Option coq_SubstLaws

  type coq_Unit = unit0

  val coq_SubstUnit : coq_Unit coq_Subst

  val coq_SubstLawsUnit : coq_Unit coq_SubstLaws

  type coq_SStore = (pVar, Coq_ty.coq_Ty, coq_Term) namedEnv

  val subst_localstore :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SStore
    coq_Subst

  val substlaws_localstore :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SStore
    coq_SubstLaws

  module TermNotations :
   sig
   end

  type coq_ETerm =
  | Coq_eterm_var of lVar * Coq_ty.coq_Ty * nat
  | Coq_eterm_val of Coq_ty.coq_Ty * Coq_ty.coq_Val
  | Coq_eterm_binop of Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_ETerm * coq_ETerm
  | Coq_eterm_unop of Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_ETerm
  | Coq_eterm_tuple of Coq_ty.coq_Ty Coq_ctx.coq_Ctx
     * (Coq_ty.coq_Ty, coq_ETerm) Coq_env.coq_Env
  | Coq_eterm_union of Coq_ty.unioni * Coq_ty.unionk * coq_ETerm
  | Coq_eterm_record of Coq_ty.recordi
     * (Coq_ty.recordf, Coq_ty.coq_Ty, coq_ETerm) namedEnv

  val erase_term :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> coq_ETerm

  val erase_SStore :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SStore ->
    (pVar, Coq_ty.coq_Ty, coq_ETerm) namedEnv

  type 'n coq_TuplePat =
  | Coq_tuplepat_nil
  | Coq_tuplepat_snoc of Coq_ty.coq_Ty Coq_ctx.coq_Ctx
     * ('n, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * 'n coq_TuplePat * Coq_ty.coq_Ty * 'n

  val coq_TuplePat_rect :
    'a2 -> (Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> 'a2 ->
    Coq_ty.coq_Ty -> 'a1 -> 'a2) -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat ->
    'a2

  val coq_TuplePat_rec :
    'a2 -> (Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> 'a2 ->
    Coq_ty.coq_Ty -> 'a1 -> 'a2) -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat ->
    'a2

  type 'n coq_RecordPat =
  | Coq_recordpat_nil
  | Coq_recordpat_snoc of (Coq_ty.recordf, Coq_ty.coq_Ty) Binding.coq_Binding
                          Coq_ctx.coq_Ctx
     * ('n, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * 'n coq_RecordPat * Coq_ty.recordf * Coq_ty.coq_Ty * 'n

  val coq_RecordPat_rect :
    'a2 -> ((Coq_ty.recordf, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> 'a2 -> Coq_ty.recordf ->
    Coq_ty.coq_Ty -> 'a1 -> 'a2) -> (Coq_ty.recordf, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> 'a2

  val coq_RecordPat_rec :
    'a2 -> ((Coq_ty.recordf, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> 'a2 -> Coq_ty.recordf ->
    Coq_ty.coq_Ty -> 'a1 -> 'a2) -> (Coq_ty.recordf, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> 'a2

  val tuple_pattern_match_env :
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> (Coq_ty.coq_Ty, 'a2)
    Coq_env.coq_Env -> ('a1, Coq_ty.coq_Ty, 'a2) namedEnv

  val tuple_pattern_match_env_reverse :
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> ('a1, Coq_ty.coq_Ty, 'a2) namedEnv
    -> (Coq_ty.coq_Ty, 'a2) Coq_env.coq_Env

  val tuple_pattern_match_val :
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> Coq_ty.coq_Val -> ('a1,
    Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv

  val record_pattern_match_env :
    (Coq_ty.recordf, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1
    coq_RecordPat -> (Coq_ty.recordf, Coq_ty.coq_Ty, 'a2) namedEnv -> ('a1,
    Coq_ty.coq_Ty, 'a2) namedEnv

  val record_pattern_match_env_reverse :
    (Coq_ty.recordf, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1
    coq_RecordPat -> ('a1, Coq_ty.coq_Ty, 'a2) namedEnv -> (Coq_ty.recordf,
    Coq_ty.coq_Ty, 'a2) namedEnv

  val record_pattern_match_val :
    Coq_ty.recordi -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> Coq_ty.coq_Val -> ('a1,
    Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv

  type 'n coq_Pattern =
  | Coq_pat_var of 'n * Coq_ty.coq_Ty
  | Coq_pat_bool
  | Coq_pat_list of Coq_ty.coq_Ty * 'n * 'n
  | Coq_pat_pair of 'n * 'n * Coq_ty.coq_Ty * Coq_ty.coq_Ty
  | Coq_pat_sum of Coq_ty.coq_Ty * Coq_ty.coq_Ty * 'n * 'n
  | Coq_pat_unit
  | Coq_pat_enum of Coq_ty.enumi
  | Coq_pat_bvec_split of nat * nat * 'n * 'n
  | Coq_pat_bvec_exhaustive of nat
  | Coq_pat_tuple of Coq_ty.coq_Ty Coq_ctx.coq_Ctx
     * ('n, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * 'n coq_TuplePat
  | Coq_pat_record of Coq_ty.recordi
     * ('n, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * 'n coq_RecordPat
  | Coq_pat_union of Coq_ty.unioni * (Coq_ty.unionk -> 'n coq_Pattern)

  val coq_Pattern_rect :
    ('a1 -> Coq_ty.coq_Ty -> 'a2) -> 'a2 -> (Coq_ty.coq_Ty -> 'a1 -> 'a1 ->
    'a2) -> ('a1 -> 'a1 -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> 'a2) ->
    (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> 'a1 -> 'a1 -> 'a2) -> 'a2 ->
    (Coq_ty.enumi -> 'a2) -> (nat -> nat -> 'a1 -> 'a1 -> 'a2) -> (nat ->
    'a2) -> (Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> 'a2) ->
    (Coq_ty.recordi -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> 'a2) -> (Coq_ty.unioni ->
    (Coq_ty.unionk -> 'a1 coq_Pattern) -> (Coq_ty.unionk -> 'a2) -> 'a2) ->
    Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a2

  val coq_Pattern_rec :
    ('a1 -> Coq_ty.coq_Ty -> 'a2) -> 'a2 -> (Coq_ty.coq_Ty -> 'a1 -> 'a1 ->
    'a2) -> ('a1 -> 'a1 -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> 'a2) ->
    (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> 'a1 -> 'a1 -> 'a2) -> 'a2 ->
    (Coq_ty.enumi -> 'a2) -> (nat -> nat -> 'a1 -> 'a1 -> 'a2) -> (nat ->
    'a2) -> (Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> 'a2) ->
    (Coq_ty.recordi -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> 'a2) -> (Coq_ty.unioni ->
    (Coq_ty.unionk -> 'a1 coq_Pattern) -> (Coq_ty.unionk -> 'a2) -> 'a2) ->
    Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a2

  type 'n coq_PatternCase = __

  val coq_EqDec_PatternCase :
    Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1 coq_PatternCase eqDec

  val coq_Finite_PatternCase :
    Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1 coq_PatternCase finite

  val coq_PatternCaseCtx :
    Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1 coq_PatternCase -> ('a1,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  type 'n coq_MatchResult =
    ('n coq_PatternCase, ('n, Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv) sigT

  val pattern_match_val :
    Coq_ty.coq_Ty -> 'a1 coq_Pattern -> Coq_ty.coq_Val -> 'a1 coq_MatchResult

  val pattern_match_val_reverse :
    Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1 coq_PatternCase -> ('a1,
    Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv -> Coq_ty.coq_Val

  val pattern_match_val_reverse' :
    Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1 coq_MatchResult -> Coq_ty.coq_Val

  type ('n, 'r) coq_PatternCaseCurried = __

  val of_pattern_case_curried :
    ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty
    -> 'a1 coq_Pattern -> ('a1, 'a2) coq_PatternCaseCurried -> 'a1
    coq_PatternCase -> 'a2

  type ('n, 'r) coq_Alternative = { alt_pat : 'n coq_Pattern;
                                    alt_rhs : ('n, 'r) coq_PatternCaseCurried }

  val alt_pat :
    ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty
    -> ('a1, 'a2) coq_Alternative -> 'a1 coq_Pattern

  val alt_rhs :
    ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty
    -> ('a1, 'a2) coq_Alternative -> ('a1, 'a2) coq_PatternCaseCurried

  val freshen_ctx :
    ('a1 -> lVar) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val unfreshen_namedenv :
    ('a1 -> lVar) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty, 'a2) namedEnv -> ('a1,
    Coq_ty.coq_Ty, 'a2) namedEnv

  val freshen_namedenv :
    ('a1 -> lVar) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty, 'a2) namedEnv -> (lVar,
    Coq_ty.coq_Ty, 'a2) namedEnv

  val freshen_tuplepat :
    ('a1 -> lVar) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> lVar
    coq_TuplePat

  val freshen_recordpat :
    ('a1 -> lVar) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (Coq_ty.recordf, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> lVar coq_RecordPat

  val freshen_pattern :
    ('a1 -> lVar) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> lVar coq_Pattern

  val unfreshen_patterncase :
    ('a1 -> lVar) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> lVar
    coq_PatternCase -> 'a1 coq_PatternCase

  val freshen_patterncase :
    ('a1 -> lVar) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1
    coq_PatternCase -> lVar coq_PatternCase

  val unfreshen_patterncaseenv' :
    ('a1 -> lVar) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> lVar
    coq_PatternCase -> (lVar, Coq_ty.coq_Ty, 'a2) namedEnv -> ('a1,
    Coq_ty.coq_Ty, 'a2) namedEnv

  val freshen_patterncaseenv :
    ('a1 -> lVar) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1
    coq_PatternCase -> ('a1, Coq_ty.coq_Ty, 'a2) namedEnv -> (lVar,
    Coq_ty.coq_Ty, 'a2) namedEnv

  val unfreshen_patterncaseenv :
    ('a1 -> lVar) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> lVar
    coq_PatternCase -> (lVar, Coq_ty.coq_Ty, 'a2) namedEnv -> ('a1,
    Coq_ty.coq_Ty, 'a2) namedEnv

  val freshen_matchresult :
    ('a1 -> lVar) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1
    coq_MatchResult -> lVar coq_MatchResult

  val unfreshen_matchresult :
    ('a1 -> lVar) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> lVar
    coq_MatchResult -> 'a1 coq_MatchResult

  type 't coq_OccursCheck =
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 't -> 't option

  val occurs_check :
    'a1 coq_OccursCheck -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1 -> 'a1 option

  val coq_OccursCheck_Const : 'a1 coq_Const coq_OccursCheck

  val occurs_check_env :
    ('a1 -> 'a2 coq_OccursCheck) -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2)
    Coq_env.coq_Env coq_OccursCheck

  val occurs_check_term : Coq_ty.coq_Ty -> coq_Term coq_OccursCheck

  val occurs_check_list : 'a1 coq_OccursCheck -> 'a1 coq_List coq_OccursCheck

  val occurs_check_sub :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub
    coq_OccursCheck

  val occurs_check_pair :
    'a1 coq_OccursCheck -> 'a2 coq_OccursCheck -> ('a1, 'a2) coq_Pair
    coq_OccursCheck

  val occurs_check_option :
    'a1 coq_OccursCheck -> 'a1 coq_Option coq_OccursCheck

  val occurs_check_unit : coq_Unit coq_OccursCheck

  val occurscheck_ctx :
    'a1 coq_OccursCheck -> 'a1 Coq_ctx.coq_Ctx coq_OccursCheck

  module Experimental :
   sig
    type 't coq_OccursCheckView =
    | Succ of 't
    | Fail of 't

    val coq_OccursCheckView_rect :
      'a1 coq_Subst -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> ('a1 -> 'a2) ->
      ('a1 -> 'a2) -> 'a1 -> 'a1 coq_OccursCheckView -> 'a2

    val coq_OccursCheckView_rec :
      'a1 coq_Subst -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> ('a1 -> 'a2) ->
      ('a1 -> 'a2) -> 'a1 -> 'a1 coq_OccursCheckView -> 'a2

    type 't coq_OccursCheck =
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 't -> 't coq_OccursCheckView

    val occurs_check_view :
      'a1 coq_Subst -> 'a1 coq_OccursCheck -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1 -> 'a1 coq_OccursCheckView

    val coq_OccursCheckEnv :
      ('a1 -> 'a2 coq_Subst) -> ('a1 -> 'a2 coq_OccursCheck) -> 'a1
      Coq_ctx.coq_Ctx -> ('a1, 'a2) Coq_env.coq_Env coq_OccursCheck
   end

  type 'sb coq_SubstUniv = { initSU : ((lVar, Coq_ty.coq_Ty)
                                      Binding.coq_Binding Coq_ctx.coq_Ctx ->
                                      'sb);
                             transSU : ((lVar, Coq_ty.coq_Ty)
                                       Binding.coq_Binding Coq_ctx.coq_Ctx ->
                                       (lVar, Coq_ty.coq_Ty)
                                       Binding.coq_Binding Coq_ctx.coq_Ctx ->
                                       (lVar, Coq_ty.coq_Ty)
                                       Binding.coq_Binding Coq_ctx.coq_Ctx ->
                                       'sb -> 'sb -> 'sb);
                             interpSU : ((lVar, Coq_ty.coq_Ty)
                                        Binding.coq_Binding Coq_ctx.coq_Ctx
                                        -> (lVar, Coq_ty.coq_Ty)
                                        Binding.coq_Binding Coq_ctx.coq_Ctx
                                        -> 'sb -> coq_Sub) }

  val initSU :
    'a1 coq_SubstUniv -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1

  val transSU :
    'a1 coq_SubstUniv -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 -> 'a1 -> 'a1

  val interpSU :
    'a1 coq_SubstUniv -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 -> coq_Sub

  type ('sb, 't) coq_SubstSU =
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 't -> 'sb -> 't

  val substSU :
    ('a1, 'a2) coq_SubstSU -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a2 -> 'a1 -> 'a2

  val substSU_term :
    'a1 coq_SubstUniv -> Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term -> 'a1 -> coq_Term

  val coq_SubstSUTerm :
    'a1 coq_SubstUniv -> Coq_ty.coq_Ty -> ('a1, coq_Term) coq_SubstSU

  val substSU_option :
    ('a1, 'a2) coq_SubstSU -> ('a1, 'a2 coq_Option) coq_SubstSU

  type 'sb coq_MeetResult = { _UU03a3_12 : (lVar, Coq_ty.coq_Ty)
                                           Binding.coq_Binding Coq_ctx.coq_Ctx;
                              meetLeft : 'sb; meetRight : 'sb; meetUp : 
                              'sb }

  val _UU03a3_12 :
    'a1 coq_SubstUniv -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_MeetResult -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx

  val meetLeft :
    'a1 coq_SubstUniv -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_MeetResult -> 'a1

  val meetRight :
    'a1 coq_SubstUniv -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_MeetResult -> 'a1

  val meetUp :
    'a1 coq_SubstUniv -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_MeetResult -> 'a1

  type 'sb coq_SubstUnivMeet =
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'sb -> 'sb -> 'sb
    coq_MeetResult

  val meetSU :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 -> 'a1 -> 'a1 coq_MeetResult

  val coq_SubstSU_env :
    'a1 coq_SubstUniv -> 'a2 Coq_ctx.coq_Ctx -> ('a2 -> ('a1, 'a3)
    coq_SubstSU) -> ('a1, ('a2, 'a3) Coq_env.coq_Env) coq_SubstSU

  val coq_SubstSU_sub :
    'a1 coq_SubstUniv -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, coq_Sub) coq_SubstSU

  val substSU_pair :
    ('a1, 'a2) coq_SubstSU -> ('a1, 'a3) coq_SubstSU -> ('a1, ('a2, 'a3)
    coq_Pair) coq_SubstSU

  val substSU_list : ('a1, 'a2) coq_SubstSU -> ('a1, 'a2 coq_List) coq_SubstSU

  val substSU_Const : ('a1, 'a2 coq_Const) coq_SubstSU

  type 'sb coq_SubstUnivVar =
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'sb

  val suVar :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUnivVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1

  type 'sb coq_SubstUnivVarUp =
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> 'sb -> 'sb

  val upSU :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUnivVar -> 'a1
    coq_SubstUnivVarUp -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> 'a1 -> 'a1

  type 'sb coq_SubstUnivVarDown = { wkVarSU : ((lVar, Coq_ty.coq_Ty)
                                              Binding.coq_Binding
                                              Coq_ctx.coq_Ctx -> (lVar,
                                              Coq_ty.coq_Ty)
                                              Binding.coq_Binding
                                              Coq_ctx.coq_Ctx -> (lVar,
                                              Coq_ty.coq_Ty)
                                              Binding.coq_Binding -> (lVar,
                                              Coq_ty.coq_Ty)
                                              Binding.coq_Binding
                                              Coq_ctx.coq_In -> 'sb -> (lVar,
                                              Coq_ty.coq_Ty)
                                              Binding.coq_Binding
                                              Coq_ctx.coq_In);
                                    downSU : ((lVar, Coq_ty.coq_Ty)
                                             Binding.coq_Binding
                                             Coq_ctx.coq_Ctx -> (lVar,
                                             Coq_ty.coq_Ty)
                                             Binding.coq_Binding
                                             Coq_ctx.coq_Ctx -> (lVar,
                                             Coq_ty.coq_Ty)
                                             Binding.coq_Binding -> (lVar,
                                             Coq_ty.coq_Ty)
                                             Binding.coq_Binding
                                             Coq_ctx.coq_In -> 'sb -> 'sb) }

  val wkVarSU :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUnivVar -> 'a1
    coq_SubstUnivVarDown -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1 -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In

  val downSU :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUnivVar -> 'a1
    coq_SubstUnivVarDown -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1 -> 'a1

  type ('sb, 't) coq_BoxSb = { unboxSb : ((lVar, Coq_ty.coq_Ty)
                                         Binding.coq_Binding Coq_ctx.coq_Ctx
                                         -> 'sb -> 't) }

  val unboxSb :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, 'a2)
    coq_BoxSb -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    'a1 -> 'a2

  val boxSb :
    ('a1, 'a2) coq_SubstSU -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a2 -> ('a1, 'a2) coq_BoxSb

  val substSU_BoxSb :
    ('a1, 'a2) coq_SubstSU -> 'a1 coq_SubstUniv -> ('a1, ('a1, 'a2)
    coq_BoxSb) coq_SubstSU

  type ('sb, 't) coq_Weakened = { _UU03a3_supp : (lVar, Coq_ty.coq_Ty)
                                                 Binding.coq_Binding
                                                 Coq_ctx.coq_Ctx;
                                  embedSupport : 'sb;
                                  wkVal : ('sb, 't) coq_BoxSb }

  val _UU03a3_supp :
    'a1 coq_SubstUniv -> ('a1, 'a2) coq_SubstSU -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Weakened -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  val embedSupport :
    'a1 coq_SubstUniv -> ('a1, 'a2) coq_SubstSU -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Weakened -> 'a1

  val wkVal :
    'a1 coq_SubstUniv -> ('a1, 'a2) coq_SubstSU -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Weakened -> ('a1,
    'a2) coq_BoxSb

  val unWeaken :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1
    coq_SubstUniv -> ('a1, 'a2) coq_SubstSU -> ('a1, 'a2) coq_Weakened -> 'a2

  val liftBoxUnOp :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 -> 'a2)
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a3,
    'a1) coq_BoxSb -> ('a3, 'a2) coq_BoxSb

  val liftBoxBinOp :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 -> 'a2
    -> 'a3) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    ('a4, 'a1) coq_BoxSb -> ('a4, 'a2) coq_BoxSb -> ('a4, 'a3) coq_BoxSb

  val weakenInit :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> ('a1, 'a2) coq_SubstSU ->
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a2 -> ('a1, 'a2) coq_Weakened

  type ('sb, 't) coq_GenOccursCheck =
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 't -> ('sb,
    't) coq_Weakened

  val gen_occurs_check :
    'a1 coq_SubstUniv -> ('a1, 'a2) coq_SubstSU -> ('a1, 'a2)
    coq_GenOccursCheck -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a2 -> ('a1, 'a2) coq_Weakened

  val coq_GenOccursCheck_Const :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> ('a1, 'a2 coq_Const) coq_GenOccursCheck

  val liftUnOp :
    'a1 coq_SubstUniv -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_SubstSU -> ('a1, 'a3) coq_SubstSU ->
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a2 -> 'a3)
    -> ('a1, 'a2) coq_Weakened -> ('a1, 'a3) coq_Weakened

  val liftBinOp :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_SubstSU -> ('a1, 'a3) coq_SubstSU ->
    ('a1, 'a4) coq_SubstSU -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a2 -> 'a3 -> 'a4) -> ('a1, 'a2) coq_Weakened -> ('a1,
    'a3) coq_Weakened -> ('a1, 'a4) coq_Weakened

  val liftTernOp :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_SubstSU -> ('a1, 'a3) coq_SubstSU ->
    ('a1, 'a4) coq_SubstSU -> ('a1, 'a5) coq_SubstSU -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a2 -> 'a3 -> 'a4
    -> 'a5) -> ('a1, 'a2) coq_Weakened -> ('a1, 'a3) coq_Weakened -> ('a1,
    'a4) coq_Weakened -> ('a1, 'a5) coq_Weakened

  val gen_occurs_check_env :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> ('a2 -> ('a1, 'a3) coq_SubstSU) -> ('a2 -> ('a1,
    'a3) coq_GenOccursCheck) -> 'a2 Coq_ctx.coq_Ctx -> ('a1, ('a2, 'a3)
    Coq_env.coq_Env) coq_GenOccursCheck

  val gen_occurs_check_term :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUnivVar -> 'a1
    coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> Coq_ty.coq_Ty -> ('a1, coq_Term) coq_GenOccursCheck

  val gen_occurs_check_list :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> ('a1, 'a2) coq_SubstSU -> ('a1, 'a2)
    coq_GenOccursCheck -> ('a1, 'a2 coq_List) coq_GenOccursCheck

  val gen_occurs_check_pair :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> ('a1, 'a2) coq_SubstSU -> ('a1, 'a3) coq_SubstSU ->
    ('a1, 'a2) coq_GenOccursCheck -> ('a1, 'a3) coq_GenOccursCheck -> ('a1,
    ('a2, 'a3) coq_Pair) coq_GenOccursCheck

  val gen_occurs_check_option :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> ('a1, 'a2) coq_SubstSU -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> ('a1, 'a2) coq_GenOccursCheck -> ('a1, 'a2
    coq_Option) coq_GenOccursCheck

  val substSU_ctx :
    ('a1, 'a2) coq_SubstSU -> ('a1, 'a2 Coq_ctx.coq_Ctx) coq_SubstSU

  val gen_occurscheck_ctx :
    ('a1, 'a2) coq_SubstSU -> 'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet ->
    ('a1, 'a2) coq_GenOccursCheck -> ('a1, 'a2 Coq_ctx.coq_Ctx)
    coq_GenOccursCheck

  val gen_occurs_check_unit :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> ('a1, coq_Unit) coq_GenOccursCheck

  type coq_WeakensTo =
  | WkNil
  | WkSkipVar of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding * coq_WeakensTo
  | WkKeepVar of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding * coq_WeakensTo

  val coq_WeakensTo_rect :
    'a1 -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1 -> 'a1) ->
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1 -> 'a1) ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> 'a1

  val coq_WeakensTo_rec :
    'a1 -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1 -> 'a1) ->
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1 -> 'a1) ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> 'a1

  val wkRefl :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo

  val wk1 :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo

  val interpWk :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_Sub

  val transWk :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakensTo -> coq_WeakensTo

  type transWk_graph =
  | Coq_transWk_graph_equation_1
  | Coq_transWk_graph_equation_2 of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
                                    Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding * coq_WeakensTo
     * coq_WeakensTo * transWk_graph
  | Coq_transWk_graph_equation_3 of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
                                    Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo * coq_WeakensTo * transWk_graph
  | Coq_transWk_graph_equation_4 of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
                                    Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo * coq_WeakensTo * transWk_graph

  val transWk_graph_rect :
    'a1 -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> coq_WeakensTo ->
    transWk_graph -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo -> transWk_graph -> 'a1
    -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    transWk_graph -> 'a1 -> 'a1) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo -> coq_WeakensTo ->
    transWk_graph -> 'a1

  val transWk_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakensTo -> transWk_graph

  val transWk_elim :
    'a1 -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> coq_WeakensTo ->
    'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    'a1 -> 'a1) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakensTo -> 'a1

  val coq_FunctionalElimination_transWk :
    __ -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> coq_WeakensTo ->
    __ -> __) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    __ -> __) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    __ -> __) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakensTo -> __

  val coq_FunctionalInduction_transWk :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakensTo -> coq_WeakensTo) functionalInduction

  val wkNilInit :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo

  val wkKeepCtx :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo

  type coq_WeakenZeroView =
  | VarUnused of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo
  | VarUsed of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo

  val coq_WeakenZeroView_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> 'a1) -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    'a1) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakenZeroView -> 'a1

  val coq_WeakenZeroView_rec :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> 'a1) -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    'a1) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakenZeroView -> 'a1

  val weakenZeroView :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> coq_WeakenZeroView

  type weakenZeroView_graph =
  | Coq_weakenZeroView_graph_equation_1 of (lVar, Coq_ty.coq_Ty)
                                           Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding * coq_WeakensTo
  | Coq_weakenZeroView_graph_equation_2 of (lVar, Coq_ty.coq_Ty)
                                           Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo

  val weakenZeroView_graph_rect :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1) -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> 'a1) -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> coq_WeakenZeroView
    -> weakenZeroView_graph -> 'a1

  val weakenZeroView_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
    weakenZeroView_graph

  val weakenZeroView_elim :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1) -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> 'a1) -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1

  val coq_FunctionalElimination_weakenZeroView :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> __) -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> __) -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> __

  val coq_FunctionalInduction_weakenZeroView :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
    coq_WeakenZeroView) functionalInduction

  type coq_WeakenNilView =
  | WkNilViewNil

  val coq_WeakenNilView_rect :
    'a1 -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakenNilView -> 'a1

  val coq_WeakenNilView_rec :
    'a1 -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakenNilView -> 'a1

  val weakenNilView :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakenNilView

  type weakenNilView_graph =
  | Coq_weakenNilView_graph_equation_1

  val weakenNilView_graph_rect :
    'a1 -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakenNilView -> weakenNilView_graph -> 'a1

  val weakenNilView_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> weakenNilView_graph

  val weakenNilView_elim :
    'a1 -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> 'a1

  val coq_FunctionalElimination_weakenNilView :
    __ -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> __

  val coq_FunctionalInduction_weakenNilView :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakenNilView) functionalInduction

  val wkRemove :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo

  val wkSingleton :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo

  val wkVarZeroIn :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In

  type wkVarZeroIn_graph =
  | Coq_wkVarZeroIn_graph_equation_1 of (lVar, Coq_ty.coq_Ty)
                                        Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding * coq_WeakensTo
     * wkVarZeroIn_graph
  | Coq_wkVarZeroIn_graph_equation_2 of (lVar, Coq_ty.coq_Ty)
                                        Binding.coq_Binding
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo

  val wkVarZeroIn_graph_rect :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> coq_WeakensTo -> wkVarZeroIn_graph -> 'a1 -> 'a1)
    -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> 'a1) -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> wkVarZeroIn_graph ->
    'a1

  val wkVarZeroIn_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> wkVarZeroIn_graph

  val wkVarZeroIn_elim :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> coq_WeakensTo -> 'a1 -> 'a1) -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> 'a1) -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1

  val coq_FunctionalElimination_wkVarZeroIn :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> coq_WeakensTo -> __ -> __) -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> __) -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> __

  val coq_FunctionalInduction_wkVarZeroIn :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In) functionalInduction

  val weakenIn :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In

  val weakenRemovePres :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo

  type coq_WeakenRemoveView =
  | MkWeakenRemoveView of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
                          Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * coq_WeakensTo

  val coq_WeakenRemoveView_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo -> 'a1) -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo ->
    coq_WeakenRemoveView -> 'a1

  val coq_WeakenRemoveView_rec :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo -> 'a1) -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo ->
    coq_WeakenRemoveView -> 'a1

  val weakenRemoveView :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakenRemoveView

  type coq_WeakenVarView =
  | WeakenVarUnused of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
                       Coq_ctx.coq_Ctx
     * coq_WeakensTo
  | WeakenVarUsed of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * coq_WeakensTo

  val coq_WeakenVarView_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> 'a1) -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo ->
    'a1) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakenVarView -> 'a1

  val coq_WeakenVarView_rec :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> 'a1) -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo ->
    'a1) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakenVarView -> 'a1

  val weakenVarView_obligations_obligation_1 :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> coq_WeakenVarView

  val weakenVarView_obligations_obligation_2 :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo -> coq_WeakenVarView)
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakenVarView

  val weakenVarView_obligations_obligation_3 :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo -> coq_WeakenVarView)
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakenVarView

  val weakenVarView :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo -> coq_WeakenVarView

  type weakenVarView_graph =
  | Coq_weakenVarView_graph_equation_1 of (lVar, Coq_ty.coq_Ty)
                                          Binding.coq_Binding
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_weakenVarView_graph_equation_2 of (lVar, Coq_ty.coq_Ty)
                                          Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * coq_WeakensTo
     * ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
       Binding.coq_Binding Coq_ctx.coq_In -> weakenVarView_graph)
  | Coq_weakenVarView_graph_equation_3 of (lVar, Coq_ty.coq_Ty)
                                          Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * coq_WeakensTo
     * ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
       Binding.coq_Binding Coq_ctx.coq_In -> weakenVarView_graph)

  val weakenVarView_graph_rect :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo
    -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> weakenVarView_graph) -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> 'a1) -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> coq_WeakensTo -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> weakenVarView_graph) -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> 'a1) -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> coq_WeakensTo -> coq_WeakenVarView ->
    weakenVarView_graph -> 'a1

  val weakenVarView_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo -> weakenVarView_graph

  val weakenVarView_elim :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo
    -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> 'a1) -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> coq_WeakensTo -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> 'a1) -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> coq_WeakensTo -> 'a1

  val coq_FunctionalElimination_weakenVarView :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo
    -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> __) -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> coq_WeakensTo -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> __) -> __) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo -> __

  val coq_FunctionalInduction_weakenVarView :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo -> coq_WeakenVarView)
    functionalInduction

  val substUniv_weaken : coq_WeakensTo coq_SubstUniv

  val extendMeetSkipSkip :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo coq_MeetResult ->
    coq_WeakensTo coq_MeetResult

  val extendMeetSkipKeep :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo coq_MeetResult ->
    coq_WeakensTo coq_MeetResult

  val extendMeetKeepSkip :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo coq_MeetResult ->
    coq_WeakensTo coq_MeetResult

  val extendMeetKeepKeep :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo coq_MeetResult ->
    coq_WeakensTo coq_MeetResult

  val meetWk :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakensTo -> coq_WeakensTo coq_MeetResult

  type meetWk_graph =
  | Coq_meetWk_graph_equation_1
  | Coq_meetWk_graph_equation_2 of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
                                   Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding * coq_WeakensTo
     * coq_WeakensTo * meetWk_graph
  | Coq_meetWk_graph_equation_3 of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
                                   Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo * coq_WeakensTo * meetWk_graph
  | Coq_meetWk_graph_equation_4 of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
                                   Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo * coq_WeakensTo * meetWk_graph
  | Coq_meetWk_graph_equation_5 of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
                                   Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo * coq_WeakensTo * meetWk_graph

  val meetWk_graph_rect :
    'a1 -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> coq_WeakensTo ->
    meetWk_graph -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakensTo -> meetWk_graph -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo -> meetWk_graph -> 'a1
    -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    meetWk_graph -> 'a1 -> 'a1) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo -> coq_WeakensTo
    coq_MeetResult -> meetWk_graph -> 'a1

  val meetWk_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakensTo -> meetWk_graph

  val meetWk_elim :
    'a1 -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> coq_WeakensTo ->
    'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    'a1 -> 'a1) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakensTo -> 'a1

  val coq_FunctionalElimination_meetWk :
    __ -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> coq_WeakensTo ->
    __ -> __) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    __ -> __) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    __ -> __) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    __ -> __) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakensTo -> __

  val coq_FunctionalInduction_meetWk :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakensTo -> coq_WeakensTo coq_MeetResult) functionalInduction

  val substUnivMeet_weaken : coq_WeakensTo coq_SubstUnivMeet

  val wkVar :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo

  val coq_FunctionalInduction_transWk_assoc : __ functionalInduction

  val substUnivVar_weaken : coq_WeakensTo coq_SubstUnivVar

  val substUnivVarUp_weaken : coq_WeakensTo coq_SubstUnivVarUp

  val substUnivVarDown_weaken : coq_WeakensTo coq_SubstUnivVarDown

  val restrictEnv :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding, 'a1) Coq_env.coq_Env ->
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding, 'a1) Coq_env.coq_Env

  val elimWeakenedVarZero :
    (coq_WeakensTo, 'a1) coq_SubstSU -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 -> 'a1) -> (coq_WeakensTo,
    'a1) coq_Weakened -> (coq_WeakensTo, 'a1) coq_Weakened

  val elimWeakenedVar :
    (coq_WeakensTo, 'a1) coq_SubstSU -> (coq_WeakensTo, 'a2) coq_SubstSU ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1 -> 'a2) -> (coq_WeakensTo, 'a1)
    coq_Weakened -> (coq_WeakensTo, 'a2) coq_Weakened

  val old_occurs_check :
    (coq_WeakensTo, 'a1) coq_SubstSU -> (coq_WeakensTo, 'a1)
    coq_GenOccursCheck -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1 -> 'a1 option

  type ('t, 'a) coq_Inst =
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 't ->
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val)
    Coq_env.coq_Env -> 'a

  val inst :
    ('a1, 'a2) coq_Inst -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding,
    Coq_ty.coq_Val) Coq_env.coq_Env -> 'a2

  type ('t, 'a) coq_Lift =
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a -> 't

  val lift :
    ('a1, 'a2) coq_Lift -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a2 -> 'a1

  val inst_list : ('a1, 'a2) coq_Inst -> ('a1 coq_List, 'a2 list) coq_Inst

  val lift_list : ('a1, 'a2) coq_Lift -> ('a1 coq_List, 'a2 list) coq_Lift

  val inst_const : ('a1 coq_Const, 'a1) coq_Inst

  val lift_const : ('a1 coq_Const, 'a1) coq_Lift

  val inst_env :
    ('a1 -> ('a2, 'a3) coq_Inst) -> 'a1 Coq_ctx.coq_Ctx -> (('a1, 'a2)
    Coq_env.coq_Env, ('a1, 'a3) Coq_env.coq_Env) coq_Inst

  val lift_env :
    ('a1 -> ('a2, 'a3) coq_Lift) -> 'a1 Coq_ctx.coq_Ctx -> (('a1, 'a2)
    Coq_env.coq_Env, ('a1, 'a3) Coq_env.coq_Env) coq_Lift

  val inst_term : Coq_ty.coq_Ty -> (coq_Term, Coq_ty.coq_Val) coq_Inst

  val lift_term : Coq_ty.coq_Ty -> (coq_Term, Coq_ty.coq_Val) coq_Lift

  val inst_sub :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_Sub,
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val)
    Coq_env.coq_Env) coq_Inst

  val inst_unit : (coq_Unit, unit0) coq_Inst

  val lift_unit : (coq_Unit, unit0) coq_Lift

  val inst_pair :
    ('a1, 'a3) coq_Inst -> ('a2, 'a4) coq_Inst -> (('a1, 'a2) coq_Pair, ('a3,
    'a4) prod) coq_Inst

  val lift_pair :
    ('a1, 'a3) coq_Lift -> ('a2, 'a4) coq_Lift -> (('a1, 'a2) coq_Pair, ('a3,
    'a4) prod) coq_Lift

  val inst_option :
    ('a1, 'a2) coq_Inst -> ('a1 coq_Option, 'a2 option) coq_Inst

  val lift_option :
    ('a1, 'a2) coq_Lift -> ('a1 coq_Option, 'a2 option) coq_Lift

  val inst_store :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_SStore,
    (pVar, Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv) coq_Inst

  val term_get_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> Coq_ty.coq_Val option

  val term_get_pair :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_Term -> (coq_Term, coq_Term) prod
    option

  val term_get_sum :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_Term -> (coq_Term, coq_Term) sum
    option

  val term_get_list :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> ((coq_Term, coq_Term) prod, unit0) sum option

  val term_get_union :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.unioni -> coq_Term -> (Coq_ty.unionk, coq_Term) sigT option

  val term_get_record :
    Coq_ty.recordi -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_Term -> (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Term)
    namedEnv option

  val term_get_tuple :
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term -> (Coq_ty.coq_Ty,
    coq_Term) Coq_env.coq_Env option

  module Entailment :
   sig
    module Coq_tactics :
     sig
     end
   end

  type ('t, 'tE) coq_Erase =
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 't -> 'tE

  val erase :
    ('a1, 'a2) coq_Erase -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 -> 'a2

  val erase_Unit : (coq_Unit, unit0) coq_Erase

  val erase_Const : ('a1 coq_Const, 'a1) coq_Erase

  val erase_Ctx :
    ('a1, 'a2) coq_Erase -> ('a1 Coq_ctx.coq_Ctx, 'a2 list) coq_Erase

  val erase_List : ('a1, 'a2) coq_Erase -> ('a1 list, 'a2 list) coq_Erase

  val erase_Term : Coq_ty.coq_Ty -> (coq_Term, coq_ETerm) coq_Erase

  val coq_EraseSStore :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_SStore,
    (pVar, Coq_ty.coq_Ty, coq_ETerm) namedEnv) coq_Erase

  module Coq_amsg :
   sig
    type 'm coq_CloseMessage =
    | Coq_there of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding * 'm

    val coq_CloseMessage_rect :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ((lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> 'a1 -> 'a2) -> 'a1
      coq_CloseMessage -> 'a2

    val coq_CloseMessage_rec :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ((lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> 'a1 -> 'a2) -> 'a1
      coq_CloseMessage -> 'a2

    val subst_closemessage : 'a1 coq_Subst -> 'a1 coq_CloseMessage coq_Subst

    val substSU_closemessage :
      (coq_WeakensTo, 'a1) coq_SubstSU -> (coq_WeakensTo, 'a1
      coq_CloseMessage) coq_SubstSU

    val substlaws_closemessage :
      'a1 coq_Subst -> 'a1 coq_SubstLaws -> 'a1 coq_CloseMessage coq_SubstLaws

    val occurscheck_closemessage :
      'a1 coq_OccursCheck -> 'a1 coq_CloseMessage coq_OccursCheck

    val erase_closemessage :
      ('a1, 'a2) coq_Erase -> ('a1 coq_CloseMessage, 'a2) coq_Erase

    type coq_AMessage =
    | Coq_mk of __ coq_Subst * (coq_WeakensTo, __) coq_SubstSU
       * __ coq_SubstLaws * __ coq_OccursCheck * (__, __) coq_Erase * 
       __

    val coq_AMessage_rect :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (__ -> __
      coq_Subst -> (coq_WeakensTo, __) coq_SubstSU -> __ -> __ coq_SubstLaws
      -> __ coq_OccursCheck -> __ -> (__, __) coq_Erase -> __ -> 'a1) ->
      coq_AMessage -> 'a1

    val coq_AMessage_rec :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (__ -> __
      coq_Subst -> (coq_WeakensTo, __) coq_SubstSU -> __ -> __ coq_SubstLaws
      -> __ coq_OccursCheck -> __ -> (__, __) coq_Erase -> __ -> 'a1) ->
      coq_AMessage -> 'a1

    val empty :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_AMessage

    val closeAux :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_WeakensTo,
      'a1) coq_SubstSU -> 'a1 coq_Subst -> 'a1 coq_SubstLaws -> 'a1
      coq_OccursCheck -> ('a1, 'a2) coq_Erase -> 'a1 -> coq_AMessage

    val close :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_AMessage ->
      coq_AMessage

    val subst_amessage : coq_AMessage coq_Subst

    val substSU_amessage : (coq_WeakensTo, coq_AMessage) coq_SubstSU

    val substlaws_amessage : coq_AMessage coq_SubstLaws

    val occurscheck_amessage : coq_AMessage coq_OccursCheck

    type coq_EAMessage =
    | MkEAMessage of __

    val coq_EAMessage_rect : (__ -> __ -> 'a1) -> coq_EAMessage -> 'a1

    val coq_EAMessage_rec : (__ -> __ -> 'a1) -> coq_EAMessage -> 'a1

    val erase_amessage : (coq_AMessage, coq_EAMessage) coq_Erase

    val boxMsg :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_AMessage ->
      coq_AMessage

    val genoccurscheck_amessage :
      (coq_WeakensTo, coq_AMessage) coq_GenOccursCheck
   end

  type coq_TermRing = { tmr_zero : Coq_ty.coq_Val; tmr_one : Coq_ty.coq_Val;
                        tmr_plus : Coq_bop.coq_BinOp;
                        tmr_times : Coq_bop.coq_BinOp;
                        tmr_minus : Coq_bop.coq_BinOp;
                        tmr_negate : Coq_uop.coq_UnOp;
                        tmr_of_Z : (z -> Coq_ty.coq_Val) }

  val tmr_zero :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> Coq_ty.coq_Val

  val tmr_one :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> Coq_ty.coq_Val

  val tmr_plus :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> Coq_bop.coq_BinOp

  val tmr_times :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> Coq_bop.coq_BinOp

  val tmr_minus :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> Coq_bop.coq_BinOp

  val tmr_negate :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> Coq_uop.coq_UnOp

  val tmr_of_Z :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> z -> Coq_ty.coq_Val

  val coq_TermRing_int :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_TermRing

  val coq_TermRing_bv :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_TermRing

  val evalPExprTm :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> coq_Term list -> z pExpr -> coq_Term

  type coq_RQuote = coq_Term list -> positive -> (z pExpr, coq_Term list) prod

  val coq_Term_Quote_def :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> coq_RQuote

  val coq_Term_Quote_unop :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> (z pExpr -> z pExpr) -> coq_RQuote -> coq_RQuote

  val coq_Term_Quote_bin :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> (z pExpr -> z pExpr -> z pExpr) ->
    coq_RQuote -> coq_RQuote -> coq_RQuote

  type coq_CanonTerm = __

  val peval_append :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> coq_Term -> coq_Term

  val peval_and_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term ->
    Coq_ty.coq_Val -> coq_Term

  val peval_or_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term ->
    Coq_ty.coq_Val -> coq_Term

  val peval_and :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term ->
    coq_Term -> coq_Term

  val peval_or :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term ->
    coq_Term -> coq_Term

  val peval_plus :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term ->
    coq_Term -> coq_Term

  type peval_plus_graph =
  | Coq_peval_plus_graph_equation_1 of lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_plus_graph_equation_2 of lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_plus_graph_equation_3 of lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In * positive
  | Coq_peval_plus_graph_equation_4 of lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In * positive
  | Coq_peval_plus_graph_equation_5 of lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_plus_graph_equation_6 of lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_plus_graph_equation_7 of lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_plus_graph_equation_8 of positive * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_plus_graph_equation_9 of positive * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_plus_graph_equation_10 of Coq_ty.coq_Val * Coq_ty.coq_Val
  | Coq_peval_plus_graph_equation_11 of Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_plus_graph_equation_12 of positive * Coq_ty.coq_Ty
     * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_plus_graph_equation_13 of positive * Coq_ty.coq_Ty
     * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_plus_graph_equation_14 of Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term
  | Coq_peval_plus_graph_equation_15 of positive * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_plus_graph_equation_16 of positive * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_plus_graph_equation_17 of Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_plus_graph_equation_18 of Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_plus_graph_equation_19 of Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term * positive
  | Coq_peval_plus_graph_equation_20 of Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term * positive
  | Coq_peval_plus_graph_equation_21 of Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term * Coq_ty.coq_Ty
     * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_plus_graph_equation_22 of Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_plus_graph_equation_23 of Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_plus_graph_equation_24 of Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term
  | Coq_peval_plus_graph_equation_25 of Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term * positive
  | Coq_peval_plus_graph_equation_26 of Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term * positive
  | Coq_peval_plus_graph_equation_27 of Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp
     * coq_Term * coq_Term
  | Coq_peval_plus_graph_equation_28 of Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term

  val peval_plus_graph_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    positive -> 'a1) -> (lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> positive -> 'a1) -> (lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (positive -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (positive ->
    lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1)
    -> (Coq_ty.coq_Val -> Coq_ty.coq_Val -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (positive -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> 'a1) -> (positive -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (positive ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (positive ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty
    -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp
    -> coq_Term -> coq_Term -> positive -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> positive ->
    'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term
    -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> positive -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> positive -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
    coq_Term -> 'a1) -> coq_Term -> coq_Term -> coq_Term -> peval_plus_graph
    -> 'a1

  val peval_plus_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term ->
    coq_Term -> peval_plus_graph

  val peval_plus_elim :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    positive -> 'a1) -> (lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> positive -> 'a1) -> (lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (positive -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (positive ->
    lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1)
    -> (Coq_ty.coq_Val -> Coq_ty.coq_Val -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (positive -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> 'a1) -> (positive -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (positive ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (positive ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty
    -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp
    -> coq_Term -> coq_Term -> positive -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> positive ->
    'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term
    -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> positive -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> positive -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
    coq_Term -> 'a1) -> coq_Term -> coq_Term -> 'a1

  val coq_FunctionalElimination_peval_plus :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) ->
    (lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    positive -> __) -> (lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> positive -> __) -> (lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __) -> (lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> (positive -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (positive ->
    lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __)
    -> (Coq_ty.coq_Val -> Coq_ty.coq_Val -> __) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) ->
    (positive -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> __) -> (positive -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) ->
    (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (positive ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (positive ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) ->
    (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> __) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp
    -> coq_Term -> coq_Term -> positive -> __) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> positive ->
    __) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term
    -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> __) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __) -> (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp
    -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> __) -> (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
    -> __) -> (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> positive ->
    __) -> (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> positive -> __)
    -> (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) ->
    (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __) -> coq_Term -> coq_Term -> __

  val coq_FunctionalInduction_peval_plus :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_Term ->
    coq_Term -> coq_Term) functionalInduction

  val peval_bvadd :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> coq_Term -> coq_Term

  type peval_bvadd_graph =
  | Coq_peval_bvadd_graph_equation_1 of nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvadd_graph_equation_2 of nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvadd_graph_equation_3 of nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In * positive
  | Coq_peval_bvadd_graph_equation_4 of nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvadd_graph_equation_5 of nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvadd_graph_equation_6 of nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvadd_graph_equation_7 of nat * positive * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvadd_graph_equation_8 of nat * Coq_ty.coq_Val * Coq_ty.coq_Val
  | Coq_peval_bvadd_graph_equation_9 of nat * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_bvadd_graph_equation_10 of nat * positive * Coq_ty.coq_Ty
     * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_bvadd_graph_equation_11 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvadd_graph_equation_12 of nat * positive * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvadd_graph_equation_13 of nat * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvadd_graph_equation_14 of nat * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_bvadd_graph_equation_15 of nat * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term * positive
  | Coq_peval_bvadd_graph_equation_16 of nat * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term * Coq_ty.coq_Ty
     * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_bvadd_graph_equation_17 of nat * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvadd_graph_equation_18 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvadd_graph_equation_19 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvadd_graph_equation_20 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * positive
  | Coq_peval_bvadd_graph_equation_21 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_bvadd_graph_equation_22 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term

  val peval_bvadd_graph_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat
    -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __
    -> 'a1) -> (nat -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> positive -> __ -> 'a1) -> (nat -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> __ ->
    lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1)
    -> (nat -> positive -> __ -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Val ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> __ -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> positive ->
    __ -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> __ -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
    coq_Term -> 'a1) -> (nat -> positive -> __ -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> __ -> 'a1) -> (nat -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> positive -> __ -> 'a1) ->
    (nat -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term
    -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __ -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> positive -> __ -> 'a1) -> (nat ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> nat -> coq_Term -> coq_Term ->
    coq_Term -> peval_bvadd_graph -> 'a1

  val peval_bvadd_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> coq_Term -> peval_bvadd_graph

  val peval_bvadd_elim :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat
    -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __
    -> 'a1) -> (nat -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> positive -> __ -> 'a1) -> (nat -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> __ ->
    lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1)
    -> (nat -> positive -> __ -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Val ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> __ -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> positive ->
    __ -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> __ -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
    coq_Term -> 'a1) -> (nat -> positive -> __ -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> __ -> 'a1) -> (nat -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> positive -> __ -> 'a1) ->
    (nat -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term
    -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __ -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> positive -> __ -> 'a1) -> (nat ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> nat -> coq_Term -> coq_Term -> 'a1

  val coq_FunctionalElimination_peval_bvadd :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat
    -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __
    -> __) -> (nat -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> positive -> __ -> __) -> (nat -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat
    -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> __ ->
    lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __)
    -> (nat -> positive -> __ -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> Coq_ty.coq_Val ->
    Coq_ty.coq_Val -> __) -> (nat -> __ -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> positive ->
    __ -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> __) -> (nat -> __ -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
    coq_Term -> __) -> (nat -> positive -> __ -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> __ -> __) -> (nat -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> positive -> __ -> __) ->
    (nat -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term
    -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __ -> __) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> positive -> __ -> __) -> (nat ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat
    -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __) -> nat -> coq_Term -> coq_Term -> __

  val coq_FunctionalInduction_peval_bvadd :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> coq_Term -> coq_Term) functionalInduction

  val peval_bvand_val_default :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term

  val peval_bvand_bvapp_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term) -> nat -> nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term

  val peval_bvand_bvcons_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term) -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> coq_Term

  val peval_bvand_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term

  type peval_bvand_val_graph =
  | Coq_peval_bvand_val_graph_equation_1 of nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_2 of nat * Coq_ty.coq_Val
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_3 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_4 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_5 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_6 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_7 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_8 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_9 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_10 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_11 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_12 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_13 of nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_14 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * Coq_ty.coq_Val

  val peval_bvand_val_graph_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val
    -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat -> __ ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term -> peval_bvand_val_graph -> 'a1

  val peval_bvand_val_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> Coq_ty.coq_Val -> peval_bvand_val_graph

  val peval_bvand_val_elim :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val
    -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat -> __ ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> nat ->
    coq_Term -> Coq_ty.coq_Val -> 'a1

  val coq_FunctionalElimination_peval_bvand_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    Coq_ty.coq_Val -> __) -> (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val -> __)
    -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat
    -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> __) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val
    -> __) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat -> nat -> __ -> coq_Term
    -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> __) -> nat -> coq_Term
    -> Coq_ty.coq_Val -> __

  val coq_FunctionalInduction_peval_bvand_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term) functionalInduction

  val peval_bvand :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> coq_Term -> coq_Term

  type peval_bvand_graph =
  | Coq_peval_bvand_graph_equation_1 of nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In * coq_Term
  | Coq_peval_bvand_graph_equation_2 of nat * Coq_ty.coq_Val * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvand_graph_equation_3 of nat * Coq_ty.coq_Val * Coq_ty.coq_Val
  | Coq_peval_bvand_graph_equation_4 of nat * Coq_ty.coq_Val * nat * 
     coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_5 of nat * Coq_ty.coq_Val * nat * 
     coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_6 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvand_graph_equation_7 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvand_graph_equation_8 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvand_graph_equation_9 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvand_graph_equation_10 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvand_graph_equation_11 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvand_graph_equation_12 of nat * nat * Coq_ty.coq_Val
     * coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_13 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvand_graph_equation_14 of nat * Coq_ty.coq_Val * nat * 
     nat * coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_15 of nat * Coq_ty.coq_Val * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvand_graph_equation_16 of nat * nat * coq_Term * coq_Term
     * coq_Term
  | Coq_peval_bvand_graph_equation_17 of nat * nat * coq_Term * coq_Term
     * coq_Term
  | Coq_peval_bvand_graph_equation_18 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_19 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_20 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_21 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_22 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_23 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_24 of nat * nat * coq_Term * coq_Term
     * lVar * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvand_graph_equation_25 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_graph_equation_26 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvand_graph_equation_27 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvand_graph_equation_28 of nat * coq_Term * coq_Term * 
     lVar * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvand_graph_equation_29 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_graph_equation_30 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvand_graph_equation_31 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvand_graph_equation_32 of nat * nat * nat * coq_Term
     * coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_33 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * coq_Term

  val peval_bvand_graph_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_Term
    -> 'a1) -> (nat -> Coq_ty.coq_Val -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Val ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term -> coq_Term
    -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat
    -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term ->
    'a1) -> (nat -> nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    Coq_ty.coq_Val -> nat -> nat -> __ -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
    -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term
    -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1)
    -> (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat -> nat -> __ ->
    coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> coq_Term -> 'a1) -> nat -> coq_Term ->
    coq_Term -> coq_Term -> peval_bvand_graph -> 'a1

  val peval_bvand_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> coq_Term -> peval_bvand_graph

  val peval_bvand_elim :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_Term
    -> 'a1) -> (nat -> Coq_ty.coq_Val -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Val ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term -> coq_Term
    -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat
    -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term ->
    'a1) -> (nat -> nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    Coq_ty.coq_Val -> nat -> nat -> __ -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
    -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term
    -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1)
    -> (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat -> nat -> __ ->
    coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> coq_Term -> 'a1) -> nat -> coq_Term ->
    coq_Term -> 'a1

  val coq_FunctionalElimination_peval_bvand :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_Term
    -> __) -> (nat -> Coq_ty.coq_Val -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> Coq_ty.coq_Val ->
    Coq_ty.coq_Val -> __) -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term ->
    coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term -> coq_Term
    -> __) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat
    -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat ->
    Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val
    -> coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> coq_Term ->
    coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> __)
    -> (nat -> nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat
    -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat ->
    Coq_ty.coq_Val -> nat -> nat -> __ -> coq_Term -> coq_Term -> __) -> (nat
    -> Coq_ty.coq_Val -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __)
    -> (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat -> nat
    -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat -> coq_Term ->
    coq_Term -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term -> coq_Term
    -> __) -> (nat -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat ->
    coq_Term -> coq_Term -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term
    -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term -> coq_Term -> __) ->
    (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat -> coq_Term -> coq_Term
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> __) -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term ->
    lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __)
    -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat
    -> nat -> nat -> __ -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> coq_Term -> __) -> nat
    -> coq_Term -> coq_Term -> __

  val coq_FunctionalInduction_peval_bvand :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> coq_Term -> coq_Term) functionalInduction

  val peval_bvor_val_default :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term

  val peval_bvor_bvapp_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term) -> nat -> nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term

  val peval_bvor_bvcons_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term) -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> coq_Term

  val peval_bvor_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term

  type peval_bvor_val_graph =
  | Coq_peval_bvor_val_graph_equation_1 of nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_2 of nat * Coq_ty.coq_Val
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_3 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_4 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_5 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_6 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_7 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_8 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_9 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_10 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_11 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_12 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_13 of nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_14 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * Coq_ty.coq_Val

  val peval_bvor_val_graph_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val
    -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat -> __ ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term -> peval_bvor_val_graph -> 'a1

  val peval_bvor_val_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> Coq_ty.coq_Val -> peval_bvor_val_graph

  val peval_bvor_val_elim :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val
    -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat -> __ ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> nat ->
    coq_Term -> Coq_ty.coq_Val -> 'a1

  val coq_FunctionalElimination_peval_bvor_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    Coq_ty.coq_Val -> __) -> (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val -> __)
    -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat
    -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> __) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val
    -> __) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat -> nat -> __ -> coq_Term
    -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> __) -> nat -> coq_Term
    -> Coq_ty.coq_Val -> __

  val coq_FunctionalInduction_peval_bvor_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term) functionalInduction

  val peval_bvor :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> coq_Term -> coq_Term

  type peval_bvor_graph =
  | Coq_peval_bvor_graph_equation_1 of nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In * coq_Term
  | Coq_peval_bvor_graph_equation_2 of nat * Coq_ty.coq_Val * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvor_graph_equation_3 of nat * Coq_ty.coq_Val * Coq_ty.coq_Val
  | Coq_peval_bvor_graph_equation_4 of nat * Coq_ty.coq_Val * nat * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_5 of nat * Coq_ty.coq_Val * nat * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_6 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_7 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_8 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_9 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_10 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_11 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_12 of nat * nat * Coq_ty.coq_Val * 
     coq_Term * coq_Term
  | Coq_peval_bvor_graph_equation_13 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_14 of nat * Coq_ty.coq_Val * nat * 
     nat * coq_Term * coq_Term
  | Coq_peval_bvor_graph_equation_15 of nat * Coq_ty.coq_Val * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvor_graph_equation_16 of nat * nat * coq_Term * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_17 of nat * nat * coq_Term * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_18 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvor_graph_equation_19 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvor_graph_equation_20 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvor_graph_equation_21 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvor_graph_equation_22 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvor_graph_equation_23 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvor_graph_equation_24 of nat * nat * coq_Term * coq_Term
     * lVar * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvor_graph_equation_25 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_graph_equation_26 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvor_graph_equation_27 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvor_graph_equation_28 of nat * coq_Term * coq_Term * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvor_graph_equation_29 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_graph_equation_30 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvor_graph_equation_31 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvor_graph_equation_32 of nat * nat * nat * coq_Term * 
     coq_Term * coq_Term
  | Coq_peval_bvor_graph_equation_33 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * coq_Term

  val peval_bvor_graph_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_Term
    -> 'a1) -> (nat -> Coq_ty.coq_Val -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Val ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term -> coq_Term
    -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat
    -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term ->
    'a1) -> (nat -> nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    Coq_ty.coq_Val -> nat -> nat -> __ -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
    -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term
    -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1)
    -> (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat -> nat -> __ ->
    coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> coq_Term -> 'a1) -> nat -> coq_Term ->
    coq_Term -> coq_Term -> peval_bvor_graph -> 'a1

  val peval_bvor_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> coq_Term -> peval_bvor_graph

  val peval_bvor_elim :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_Term
    -> 'a1) -> (nat -> Coq_ty.coq_Val -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Val ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term -> coq_Term
    -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat
    -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term ->
    'a1) -> (nat -> nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    Coq_ty.coq_Val -> nat -> nat -> __ -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
    -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term
    -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1)
    -> (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat -> nat -> __ ->
    coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> coq_Term -> 'a1) -> nat -> coq_Term ->
    coq_Term -> 'a1

  val coq_FunctionalElimination_peval_bvor :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_Term
    -> __) -> (nat -> Coq_ty.coq_Val -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> Coq_ty.coq_Val ->
    Coq_ty.coq_Val -> __) -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term ->
    coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term -> coq_Term
    -> __) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat
    -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat ->
    Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val
    -> coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> coq_Term ->
    coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> __)
    -> (nat -> nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat
    -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat ->
    Coq_ty.coq_Val -> nat -> nat -> __ -> coq_Term -> coq_Term -> __) -> (nat
    -> Coq_ty.coq_Val -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __)
    -> (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat -> nat
    -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat -> coq_Term ->
    coq_Term -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term -> coq_Term
    -> __) -> (nat -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat ->
    coq_Term -> coq_Term -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term
    -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term -> coq_Term -> __) ->
    (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat -> coq_Term -> coq_Term
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> __) -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term ->
    lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __)
    -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat
    -> nat -> nat -> __ -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> coq_Term -> __) -> nat
    -> coq_Term -> coq_Term -> __

  val coq_FunctionalInduction_peval_bvor :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> coq_Term -> coq_Term) functionalInduction

  val peval_bvapp_val_r :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> coq_Term -> Coq_ty.coq_Val -> coq_Term

  val peval_bvapp :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> coq_Term -> coq_Term -> coq_Term

  type peval_bvapp_graph =
  | Coq_peval_bvapp_graph_equation_1 of nat * nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_2 of nat * nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_3 of nat * nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvapp_graph_equation_4 of nat * nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_5 of nat * nat * Coq_ty.coq_Val * 
     lVar * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_6 of nat * nat * Coq_ty.coq_Val
     * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_7 of nat * nat * Coq_ty.coq_Val
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvapp_graph_equation_8 of nat * nat * Coq_ty.coq_Val
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_9 of nat * nat * nat * coq_Term * 
     coq_Term * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_10 of nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_11 of nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp
     * coq_Term * coq_Term
  | Coq_peval_bvapp_graph_equation_12 of nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_13 of nat * nat * nat * coq_Term
     * coq_Term * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_14 of nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_15 of nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp
     * coq_Term * coq_Term
  | Coq_peval_bvapp_graph_equation_16 of nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_17 of nat * nat * coq_Term * coq_Term
     * lVar * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_18 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_19 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvapp_graph_equation_20 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_21 of nat * nat * coq_Term * coq_Term
     * lVar * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_22 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_23 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvapp_graph_equation_24 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_25 of nat * nat * coq_Term * coq_Term
     * lVar * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_26 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_27 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvapp_graph_equation_28 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_29 of nat * nat * coq_Term * coq_Term
     * lVar * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_30 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_31 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvapp_graph_equation_32 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_33 of nat * nat * coq_Term * coq_Term
     * lVar * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_34 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_35 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvapp_graph_equation_36 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_37 of nat * nat * coq_Term * coq_Term
     * lVar * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_38 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_39 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvapp_graph_equation_40 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_41 of nat * nat * nat * coq_Term
     * coq_Term * coq_Term
  | Coq_peval_bvapp_graph_equation_42 of nat * nat * coq_Term * coq_Term
     * lVar * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_43 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_44 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvapp_graph_equation_45 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_46 of nat * nat * nat * nat * coq_Term
     * coq_Term * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_47 of nat * nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_48 of nat * nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp
     * coq_Term * coq_Term
  | Coq_peval_bvapp_graph_equation_49 of nat * nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_50 of nat * nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_51 of nat * nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_52 of nat * nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_bvapp_graph_equation_53 of nat * nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term

  val peval_bvapp_graph_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> nat
    -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1)
    -> (nat -> nat -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1)
    -> (nat -> nat -> Coq_ty.coq_Val -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat ->
    Coq_ty.coq_Val -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> Coq_ty.coq_Val
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> Coq_ty.coq_Val -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat -> nat -> coq_Term ->
    coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat ->
    nat -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
    -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat -> nat -> nat ->
    __ -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> nat -> nat
    -> __ -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    nat -> nat -> __ -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> nat -> nat -> __ -> coq_Term -> coq_Term -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> 'a1)
    -> (nat -> nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
    coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> nat
    -> nat -> coq_Term -> coq_Term -> coq_Term -> peval_bvapp_graph -> 'a1

  val peval_bvapp_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> coq_Term -> coq_Term -> peval_bvapp_graph

  val peval_bvapp_elim :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> nat
    -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1)
    -> (nat -> nat -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1)
    -> (nat -> nat -> Coq_ty.coq_Val -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat ->
    Coq_ty.coq_Val -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> Coq_ty.coq_Val
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> Coq_ty.coq_Val -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat -> nat -> coq_Term ->
    coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat ->
    nat -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
    -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat -> nat -> nat ->
    __ -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> nat -> nat
    -> __ -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    nat -> nat -> __ -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> nat -> nat -> __ -> coq_Term -> coq_Term -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> 'a1)
    -> (nat -> nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
    coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> nat
    -> nat -> coq_Term -> coq_Term -> 'a1

  val coq_FunctionalElimination_peval_bvapp :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> nat
    -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __)
    -> (nat -> nat -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> Coq_ty.coq_Val -> __) -> (nat -> nat -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat
    -> nat -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) ->
    (nat -> nat -> Coq_ty.coq_Val -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat ->
    Coq_ty.coq_Val -> Coq_ty.coq_Val -> __) -> (nat -> nat -> Coq_ty.coq_Val
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> __) -> (nat -> nat -> Coq_ty.coq_Val -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> nat -> nat -> coq_Term ->
    coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> __) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> __) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> __) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> nat ->
    nat -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    __) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    __) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    __) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    __) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    __) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    __) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    __) -> (nat -> nat -> nat -> coq_Term -> coq_Term -> coq_Term -> __) ->
    (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat -> coq_Term -> coq_Term
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> __) -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> nat -> nat -> nat -> __
    -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat -> nat -> nat ->
    __ -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat -> nat
    -> nat -> __ -> coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat -> nat ->
    nat -> __ -> coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
    coq_Term -> __) -> (nat -> nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
    coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> __) -> (nat -> nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp
    -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __) -> nat -> nat -> coq_Term -> coq_Term
    -> __

  val coq_FunctionalInduction_peval_bvapp :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> nat
    -> coq_Term -> coq_Term -> coq_Term) functionalInduction

  val peval_bvdrop_bvapp :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> nat
    -> nat -> coq_Term -> __ -> coq_Term) -> nat -> nat -> nat -> nat ->
    coq_Term -> coq_Term -> coq_Term

  val peval_bvdrop_bvcons :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> nat
    -> nat -> coq_Term -> __ -> coq_Term) -> nat -> nat -> nat -> coq_Term ->
    coq_Term -> coq_Term

  val peval_bvdrop_bvdrop :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> nat
    -> nat -> coq_Term -> __ -> coq_Term) -> nat -> nat -> nat -> nat ->
    coq_Term -> coq_Term

  val peval_bvdrop_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> nat -> Coq_ty.coq_Val -> coq_Term

  val peval_bvdrop_default :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> nat -> coq_Term -> coq_Term

  val peval_bvdrop_eq :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> nat -> coq_Term -> coq_Term

  val peval_bvdrop :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> coq_Term -> coq_Term

  val peval_bvtake_bvapp :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> nat
    -> nat -> coq_Term -> __ -> coq_Term) -> nat -> nat -> nat -> nat ->
    coq_Term -> coq_Term -> coq_Term

  val peval_bvtake_bvcons :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> nat
    -> nat -> coq_Term -> __ -> coq_Term) -> nat -> nat -> nat -> coq_Term ->
    coq_Term -> coq_Term

  val peval_bvtake_bvtake :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> nat
    -> nat -> coq_Term -> __ -> coq_Term) -> nat -> nat -> nat -> nat ->
    coq_Term -> coq_Term

  val peval_bvtake_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> nat -> Coq_ty.coq_Val -> coq_Term

  val peval_bvtake_default :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> nat -> coq_Term -> coq_Term

  val peval_bvtake_eq :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> nat -> coq_Term -> coq_Term

  val peval_bvtake :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> coq_Term -> coq_Term

  val peval_update_vector_subrange :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> nat -> coq_Term -> coq_Term -> coq_Term

  val peval_binop' :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> coq_Term

  val peval_binop :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> coq_Term

  val peval_not :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term ->
    coq_Term

  type peval_not_graph =
  | Coq_peval_not_graph_equation_1 of lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_not_graph_equation_2 of Coq_ty.coq_Val
  | Coq_peval_not_graph_equation_3 of coq_Term * coq_Term * peval_not_graph
     * peval_not_graph
  | Coq_peval_not_graph_equation_4 of coq_Term * coq_Term * peval_not_graph
     * peval_not_graph
  | Coq_peval_not_graph_equation_5 of Coq_ty.coq_Ty * Coq_bop.coq_RelOp
     * coq_Term * coq_Term
  | Coq_peval_not_graph_equation_6 of Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term

  val peval_not_graph_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (Coq_ty.coq_Val -> 'a1) -> (coq_Term -> coq_Term -> peval_not_graph ->
    'a1 -> peval_not_graph -> 'a1 -> 'a1) -> (coq_Term -> coq_Term ->
    peval_not_graph -> 'a1 -> peval_not_graph -> 'a1 -> 'a1) ->
    (Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> coq_Term -> coq_Term -> 'a1) ->
    (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> coq_Term ->
    coq_Term -> peval_not_graph -> 'a1

  val peval_not_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term ->
    peval_not_graph

  val peval_not_elim :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (Coq_ty.coq_Val -> 'a1) -> (coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) ->
    (coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_bop.coq_RelOp -> coq_Term -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> coq_Term -> 'a1

  val coq_FunctionalElimination_peval_not :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) ->
    (Coq_ty.coq_Val -> __) -> (coq_Term -> coq_Term -> __ -> __ -> __) ->
    (coq_Term -> coq_Term -> __ -> __ -> __) -> (Coq_ty.coq_Ty ->
    Coq_bop.coq_RelOp -> coq_Term -> coq_Term -> __) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __) -> coq_Term -> __

  val coq_FunctionalInduction_peval_not :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_Term ->
    coq_Term) functionalInduction

  val peval_unsigned_bvapp :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> coq_Term -> coq_Term -> coq_Term

  val peval_unsigned :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> coq_Term

  type peval_unsigned_graph =
  | Coq_peval_unsigned_graph_equation_1 of nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_unsigned_graph_equation_2 of nat * Coq_ty.coq_Val
  | Coq_peval_unsigned_graph_equation_3 of nat * nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_4 of nat * nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_5 of nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_6 of nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_7 of nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_8 of nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_9 of nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_10 of nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_11 of nat * nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_12 of nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_13 of nat * nat * nat * coq_Term
     * coq_Term
  | Coq_peval_unsigned_graph_equation_14 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term

  val peval_unsigned_graph_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (nat -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term
    -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term
    -> coq_Term -> 'a1) -> (nat -> nat -> nat -> __ -> coq_Term -> coq_Term
    -> 'a1) -> (nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1)
    -> nat -> coq_Term -> coq_Term -> peval_unsigned_graph -> 'a1

  val peval_unsigned_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> peval_unsigned_graph

  val peval_unsigned_elim :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (nat -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term
    -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term
    -> coq_Term -> 'a1) -> (nat -> nat -> nat -> __ -> coq_Term -> coq_Term
    -> 'a1) -> (nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1)
    -> nat -> coq_Term -> 'a1

  val coq_FunctionalElimination_peval_unsigned :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) ->
    (nat -> Coq_ty.coq_Val -> __) -> (nat -> nat -> coq_Term -> coq_Term ->
    __) -> (nat -> nat -> coq_Term -> coq_Term -> __) -> (nat -> coq_Term ->
    coq_Term -> __) -> (nat -> coq_Term -> coq_Term -> __) -> (nat ->
    coq_Term -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term -> __) ->
    (nat -> coq_Term -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term ->
    __) -> (nat -> nat -> coq_Term -> coq_Term -> __) -> (nat -> coq_Term ->
    coq_Term -> __) -> (nat -> nat -> nat -> __ -> coq_Term -> coq_Term ->
    __) -> (nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) ->
    nat -> coq_Term -> __

  val coq_FunctionalInduction_peval_unsigned :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> coq_Term) functionalInduction

  val peval_vector_subrange :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> nat -> coq_Term -> coq_Term

  val peval_unop' :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> coq_Term

  val peval_zext :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> coq_Term -> coq_Term

  val peval_unop :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> coq_Term

  val evalPolTm :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> coq_Term list -> z pol -> coq_Term

  val coq_CanonTerm_to_Term :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_CanonTerm -> coq_Term

  val peval_union :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.unioni -> Coq_ty.unionk -> coq_Term -> coq_Term

  val peval_record' :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (Coq_ty.recordf, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Term) namedEnv -> (Coq_ty.recordf,
    Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv option

  val peval_record :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.recordi -> (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Term) namedEnv ->
    coq_Term

  val coq_CanonTerm_def :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> coq_CanonTerm

  val peval2_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Val -> coq_CanonTerm

  val peval2_binop :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_CanonTerm -> coq_CanonTerm -> coq_CanonTerm

  val peval2_unop :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_CanonTerm ->
    coq_CanonTerm

  val peval2 :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> coq_CanonTerm

  val peval :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> coq_Term

  val pevals :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, coq_Term)
    Coq_env.coq_Env -> (Coq_ty.coq_Ty, coq_Term) Coq_env.coq_Env

  type 'n coq_SMatchResult =
    ('n coq_PatternCase, ('n, Coq_ty.coq_Ty, coq_Term) namedEnv) sigT

  val pattern_match_term_reverse :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1 coq_PatternCase -> ('a1,
    Coq_ty.coq_Ty, coq_Term) namedEnv -> coq_Term

  val seval_exp :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SStore ->
    Coq_ty.coq_Ty -> coq_Exp -> coq_Term

  val seval_exps :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SStore -> ('a1,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1,
    Coq_ty.coq_Ty, coq_Exp) namedEnv -> ('a1, Coq_ty.coq_Ty, coq_Term)
    namedEnv

  type 'p coq_Precise = { prec_input : Coq_ty.coq_Ty Coq_ctx.coq_Ctx;
                          prec_output : Coq_ty.coq_Ty Coq_ctx.coq_Ctx }

  val prec_input :
    ('a1 -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx) -> 'a1 -> 'a1 coq_Precise ->
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx

  val prec_output :
    ('a1 -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx) -> 'a1 -> 'a1 coq_Precise ->
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx
 end

module String :
 sig
  val inhabited : string inhabited
 end

type chain = { chain_car : (nat -> __) }

type cofe = { compl : (chain -> __) }

val discrete_cofe : __ -> cofe

type bi = { bi_emp : __; bi_pure : (__ -> __); bi_and : (__ -> __ -> __);
            bi_or : (__ -> __ -> __); bi_impl : (__ -> __ -> __);
            bi_forall : (__ -> (__ -> __) -> __);
            bi_exist : (__ -> (__ -> __) -> __); bi_sep : (__ -> __ -> __);
            bi_wand : (__ -> __ -> __); bi_persistently : (__ -> __);
            bi_later : (__ -> __); bi_cofe_aux : cofe }

type modality_action =
| MIEnvIsEmpty of bi
| MIEnvForall
| MIEnvTransform of bi
| MIEnvClear of bi
| MIEnvId

type modality = { modality_car : (__ -> __);
                  modality_intuitionistic_action : modality_action;
                  modality_spatial_action : modality_action }

type 't isDuplicable = { is_duplicable : ('t -> bool) }

val heap_extractions :
  'a1 isDuplicable -> 'a1 list -> ('a1, 'a1 list) prod list

module type FailLogic =
 sig
  val fail_rule_pre : bool
 end

module DefaultFailLogic :
 sig
  val fail_rule_pre : bool
 end

module MakeExecutor :
 functor (B:Base) ->
 functor (SIG:sig
  type _UU1d477_

  val _UU1d477__Ty : _UU1d477_ -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx

  val _UU1d477__inst :
    _UU1d477_ -> (Coq_ty.coq_Ty, Coq_ty.coq_Val, __) Coq_env.abstract

  val _UU1d477__eq_dec : _UU1d477_ eqDec

  type _UU1d46f_

  val _UU1d46f__Ty : _UU1d46f_ -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx

  val _UU1d46f__is_dup : _UU1d46f_ isDuplicable

  val _UU1d46f__eq_dec : _UU1d46f_ eqDec

  val _UU1d46f__precise : _UU1d46f_ -> _UU1d46f_ B.coq_Precise option

  type coq_PredicateDef = { lptsreg : (Coq_ty.coq_Ty ->
                                      B._UU1d479__UU1d46c__UU1d46e_ ->
                                      Coq_ty.coq_Val -> __);
                            luser : (_UU1d46f_ -> (Coq_ty.coq_Ty,
                                    Coq_ty.coq_Val) Coq_env.coq_Env -> __) }

  val lptsreg :
    bi -> coq_PredicateDef -> Coq_ty.coq_Ty -> B._UU1d479__UU1d46c__UU1d46e_
    -> Coq_ty.coq_Val -> __

  val luser :
    bi -> coq_PredicateDef -> _UU1d46f_ -> (Coq_ty.coq_Ty, Coq_ty.coq_Val)
    Coq_env.coq_Env -> __

  type coq_Formula =
  | Coq_formula_user of _UU1d477_
     * (Coq_ty.coq_Ty, B.coq_Term) Coq_env.coq_Env
  | Coq_formula_bool of B.coq_Term
  | Coq_formula_prop of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
                        Coq_ctx.coq_Ctx
     * B.coq_Sub * (lVar, Coq_ty.coq_Ty, Coq_ty.coq_Val, __) abstract_named
  | Coq_formula_relop of Coq_ty.coq_Ty * Coq_bop.coq_RelOp * B.coq_Term
     * B.coq_Term
  | Coq_formula_true
  | Coq_formula_false
  | Coq_formula_and of coq_Formula * coq_Formula
  | Coq_formula_or of coq_Formula * coq_Formula

  val coq_Formula_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (_UU1d477_
    -> (Coq_ty.coq_Ty, B.coq_Term) Coq_env.coq_Env -> 'a1) -> (B.coq_Term ->
    'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    B.coq_Sub -> (lVar, Coq_ty.coq_Ty, Coq_ty.coq_Val, __) abstract_named ->
    'a1) -> (Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> B.coq_Term -> B.coq_Term
    -> 'a1) -> 'a1 -> 'a1 -> (coq_Formula -> 'a1 -> coq_Formula -> 'a1 ->
    'a1) -> (coq_Formula -> 'a1 -> coq_Formula -> 'a1 -> 'a1) -> coq_Formula
    -> 'a1

  val coq_Formula_rec :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (_UU1d477_
    -> (Coq_ty.coq_Ty, B.coq_Term) Coq_env.coq_Env -> 'a1) -> (B.coq_Term ->
    'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    B.coq_Sub -> (lVar, Coq_ty.coq_Ty, Coq_ty.coq_Val, __) abstract_named ->
    'a1) -> (Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> B.coq_Term -> B.coq_Term
    -> 'a1) -> 'a1 -> 'a1 -> (coq_Formula -> 'a1 -> coq_Formula -> 'a1 ->
    'a1) -> (coq_Formula -> 'a1 -> coq_Formula -> 'a1 -> 'a1) -> coq_Formula
    -> 'a1

  val formula_relop_neg :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> B.coq_Term -> B.coq_Term ->
    coq_Formula

  val subSU_formula : 'a1 B.coq_SubstUniv -> ('a1, coq_Formula) B.coq_SubstSU

  val sub_formula : coq_Formula B.coq_Subst

  val substlaws_formula : coq_Formula B.coq_SubstLaws

  val coq_OccursCheckFormula : coq_Formula B.coq_OccursCheck

  val coq_GenOccursCheckFormula :
    'a1 B.coq_SubstUniv -> 'a1 B.coq_SubstUnivMeet -> 'a1 B.coq_SubstUnivVar
    -> 'a1 B.coq_SubstUniv -> 'a1 B.coq_SubstUnivMeet -> 'a1 B.coq_SubstUniv
    -> 'a1 B.coq_SubstUnivMeet -> ('a1, coq_Formula) B.coq_GenOccursCheck

  type coq_PathCondition = coq_Formula Coq_ctx.coq_Ctx

  val formula_eqs_ctx :
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, B.coq_Term)
    Coq_env.coq_Env -> (Coq_ty.coq_Ty, B.coq_Term) Coq_env.coq_Env ->
    coq_PathCondition

  val formula_eqs_nctx :
    ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1,
    Coq_ty.coq_Ty, B.coq_Term) namedEnv -> ('a1, Coq_ty.coq_Ty, B.coq_Term)
    namedEnv -> coq_PathCondition

  type coq_EFormula =
  | Coq_eformula_user of _UU1d477_
     * (Coq_ty.coq_Ty, B.coq_ETerm) Coq_env.coq_Env
  | Coq_eformula_bool of B.coq_ETerm
  | Coq_eformula_prop of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
                         Coq_ctx.coq_Ctx
     * ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding, B.coq_ETerm)
       Coq_env.coq_Env
     * (lVar, Coq_ty.coq_Ty, Coq_ty.coq_Val, __) abstract_named
  | Coq_eformula_relop of Coq_ty.coq_Ty * Coq_bop.coq_RelOp * B.coq_ETerm
     * B.coq_ETerm
  | Coq_eformula_true
  | Coq_eformula_false
  | Coq_eformula_and of coq_EFormula * coq_EFormula
  | Coq_eformula_or of coq_EFormula * coq_EFormula

  val coq_EFormula_rect :
    (_UU1d477_ -> (Coq_ty.coq_Ty, B.coq_ETerm) Coq_env.coq_Env -> 'a1) ->
    (B.coq_ETerm -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding,
    B.coq_ETerm) Coq_env.coq_Env -> (lVar, Coq_ty.coq_Ty, Coq_ty.coq_Val, __)
    abstract_named -> 'a1) -> (Coq_ty.coq_Ty -> Coq_bop.coq_RelOp ->
    B.coq_ETerm -> B.coq_ETerm -> 'a1) -> 'a1 -> 'a1 -> (coq_EFormula -> 'a1
    -> coq_EFormula -> 'a1 -> 'a1) -> (coq_EFormula -> 'a1 -> coq_EFormula ->
    'a1 -> 'a1) -> coq_EFormula -> 'a1

  val coq_EFormula_rec :
    (_UU1d477_ -> (Coq_ty.coq_Ty, B.coq_ETerm) Coq_env.coq_Env -> 'a1) ->
    (B.coq_ETerm -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding,
    B.coq_ETerm) Coq_env.coq_Env -> (lVar, Coq_ty.coq_Ty, Coq_ty.coq_Val, __)
    abstract_named -> 'a1) -> (Coq_ty.coq_Ty -> Coq_bop.coq_RelOp ->
    B.coq_ETerm -> B.coq_ETerm -> 'a1) -> 'a1 -> 'a1 -> (coq_EFormula -> 'a1
    -> coq_EFormula -> 'a1 -> 'a1) -> (coq_EFormula -> 'a1 -> coq_EFormula ->
    'a1 -> 'a1) -> coq_EFormula -> 'a1

  val erase_formula :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Formula
    -> coq_EFormula

  val erase_Formula : (coq_Formula, coq_EFormula) B.coq_Erase

  type 'v coq_GChunk =
  | Coq_chunk_user of _UU1d46f_ * (Coq_ty.coq_Ty, 'v) Coq_env.coq_Env
  | Coq_chunk_ptsreg of Coq_ty.coq_Ty * B._UU1d479__UU1d46c__UU1d46e_ * 'v
  | Coq_chunk_conj of 'v coq_GChunk * 'v coq_GChunk
  | Coq_chunk_wand of 'v coq_GChunk * 'v coq_GChunk

  val coq_GChunk_rect :
    (_UU1d46f_ -> (Coq_ty.coq_Ty, 'a1) Coq_env.coq_Env -> 'a2) ->
    (Coq_ty.coq_Ty -> B._UU1d479__UU1d46c__UU1d46e_ -> 'a1 -> 'a2) -> ('a1
    coq_GChunk -> 'a2 -> 'a1 coq_GChunk -> 'a2 -> 'a2) -> ('a1 coq_GChunk ->
    'a2 -> 'a1 coq_GChunk -> 'a2 -> 'a2) -> 'a1 coq_GChunk -> 'a2

  val coq_GChunk_rec :
    (_UU1d46f_ -> (Coq_ty.coq_Ty, 'a1) Coq_env.coq_Env -> 'a2) ->
    (Coq_ty.coq_Ty -> B._UU1d479__UU1d46c__UU1d46e_ -> 'a1 -> 'a2) -> ('a1
    coq_GChunk -> 'a2 -> 'a1 coq_GChunk -> 'a2 -> 'a2) -> ('a1 coq_GChunk ->
    'a2 -> 'a1 coq_GChunk -> 'a2 -> 'a2) -> 'a1 coq_GChunk -> 'a2

  type coq_SCChunk = Coq_ty.coq_Val coq_GChunk

  type coq_Chunk = B.coq_Term coq_GChunk

  val coq_NoConfusionPackage_GChunk : 'a1 coq_GChunk noConfusionPackage

  val chunk_isdup : 'a1 coq_GChunk isDuplicable

  val chunk_eqb :
    (Coq_ty.coq_Ty -> 'a1 -> 'a1 -> bool) -> 'a1 coq_GChunk -> 'a1 coq_GChunk
    -> bool

  val chunk_eqb_spec :
    (Coq_ty.coq_Ty -> 'a1 -> 'a1 -> bool) -> (Coq_ty.coq_Ty -> 'a1 -> 'a1 ->
    reflect) -> 'a1 coq_GChunk -> 'a1 coq_GChunk -> reflect

  val coq_SubstChunk : coq_Chunk B.coq_Subst

  val coq_SubstSUChunk : 'a1 B.coq_SubstUniv -> ('a1, coq_Chunk) B.coq_SubstSU

  val substlaws_chunk : coq_Chunk B.coq_SubstLaws

  val map_GChunk :
    (Coq_ty.coq_Ty -> 'a1 -> 'a2) -> 'a1 coq_GChunk -> 'a2 coq_GChunk

  val inst_chunk : (coq_Chunk, coq_SCChunk) B.coq_Inst

  val coq_OccursCheckChunk : coq_Chunk B.coq_OccursCheck

  val coq_GenOccursCheckChunk :
    (B.coq_WeakensTo, coq_Chunk) B.coq_GenOccursCheck

  type coq_SCHeap = coq_SCChunk list

  type coq_SHeap = coq_Chunk list

  val inst_heap : (coq_SHeap, coq_SCHeap) B.coq_Inst

  val peval_chunk :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Chunk ->
    coq_Chunk

  val try_consume_chunk_exact :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SHeap ->
    coq_Chunk -> coq_SHeap option

  val match_chunk_user_precise_clause_1 :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> _UU1d46f_ ->
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx ->
    (Coq_ty.coq_Ty, B.coq_Term) Coq_env.coq_Env -> (Coq_ty.coq_Ty,
    B.coq_Term) Coq_env.coq_Env -> _UU1d46f_ -> sumbool -> (Coq_ty.coq_Ty,
    B.coq_Term) Coq_env.coq_Env -> coq_PathCondition option

  val match_chunk_user_precise :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> _UU1d46f_ ->
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx ->
    (Coq_ty.coq_Ty, B.coq_Term) Coq_env.coq_Env -> (Coq_ty.coq_Ty,
    B.coq_Term) Coq_env.coq_Env -> coq_Chunk -> coq_PathCondition option

  val try_consume_chunk_user_precise :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> _UU1d46f_ ->
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx ->
    (Coq_ty.coq_Ty, B.coq_Term) Coq_env.coq_Env -> (Coq_ty.coq_Ty,
    B.coq_Term) Coq_env.coq_Env -> coq_SHeap -> (coq_SHeap,
    coq_PathCondition) prod option

  val match_chunk_ptsreg_precise_clause_1 :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> B._UU1d479__UU1d46c__UU1d46e_ -> Coq_ty.coq_Ty ->
    B._UU1d479__UU1d46c__UU1d46e_ -> sumbool -> B.coq_Term -> B.coq_Term
    option

  val match_chunk_ptsreg_precise :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> B._UU1d479__UU1d46c__UU1d46e_ -> coq_Chunk -> B.coq_Term
    option

  val find_chunk_ptsreg_precise :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> B._UU1d479__UU1d46c__UU1d46e_ -> coq_SHeap ->
    (B.coq_Term, coq_SHeap) prod option

  val try_consume_chunk_ptsreg_precise :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> B._UU1d479__UU1d46c__UU1d46e_ -> coq_SHeap -> B.coq_Term
    -> (coq_SHeap, coq_PathCondition) prod option

  val try_consume_chunk_precise :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SHeap ->
    coq_Chunk -> (coq_SHeap, coq_PathCondition) prod option

  val interpret_chunk :
    bi -> coq_PredicateDef -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_Chunk -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env -> __

  val interpret_scchunk : bi -> coq_PredicateDef -> coq_SCChunk -> __

  val interpret_scheap : bi -> coq_PredicateDef -> coq_SCHeap -> __

  type coq_EChunk = B.coq_ETerm coq_GChunk

  val coq_Erase_Chunk : (coq_Chunk, coq_EChunk) B.coq_Erase

  type coq_World = { wctx : (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
                            Coq_ctx.coq_Ctx;
                     wco : coq_PathCondition }

  val wctx :
    coq_World -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  val wco : coq_World -> coq_PathCondition

  val wnil : coq_World

  val wlctx :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_World

  val wsnoc :
    coq_World -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_World

  val term_var_zero :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> B.coq_Term

  val wlet :
    coq_World -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> Coq_ty.coq_Val
    -> coq_World

  val wcat :
    coq_World -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_World

  val wformula : coq_World -> coq_Formula -> coq_World

  val wpathcondition : coq_World -> coq_PathCondition -> coq_World

  val wsubst :
    coq_World -> lVar -> Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> B.coq_Term -> coq_World

  val wmatch :
    coq_World -> Coq_ty.coq_Ty -> B.coq_Term -> lVar B.coq_Pattern -> lVar
    B.coq_PatternCase -> coq_World

  val wmatchvar_patternvars :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar ->
    Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> lVar B.coq_Pattern -> lVar B.coq_PatternCase -> B.coq_Sub

  val wmatchvar :
    coq_World -> lVar -> Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> lVar B.coq_Pattern -> lVar
    B.coq_PatternCase -> coq_World

  type 'a coq_Valid = coq_World -> 'a

  type ('a, 'b) coq_Impl = 'a -> 'b

  type ('i, 'a) coq_Forall = 'i -> 'a

  type coq_Tri =
  | Coq_tri_id
  | Coq_tri_cons of coq_World * lVar * Coq_ty.coq_Ty
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In * B.coq_Term
     * coq_Tri

  val coq_Tri_rect :
    (coq_World -> 'a1) -> (coq_World -> coq_World -> lVar -> Coq_ty.coq_Ty ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> B.coq_Term ->
    coq_Tri -> 'a1 -> 'a1) -> coq_World -> coq_World -> coq_Tri -> 'a1

  val coq_Tri_rec :
    (coq_World -> 'a1) -> (coq_World -> coq_World -> lVar -> Coq_ty.coq_Ty ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> B.coq_Term ->
    coq_Tri -> 'a1 -> 'a1) -> coq_World -> coq_World -> coq_Tri -> 'a1

  val tri_comp :
    coq_World -> coq_World -> coq_World -> coq_Tri -> coq_Tri -> coq_Tri

  val sub_wmatch_patctx :
    coq_World -> Coq_ty.coq_Ty -> B.coq_Term -> lVar B.coq_Pattern -> lVar
    B.coq_PatternCase -> B.coq_Sub

  val sub_triangular : coq_World -> coq_World -> coq_Tri -> B.coq_Sub

  val sub_triangular_inv : coq_World -> coq_World -> coq_Tri -> B.coq_Sub

  type coq_Acc =
  | Coq_acc_refl
  | Coq_acc_sub of coq_World * B.coq_Sub

  val coq_Acc_rect :
    coq_World -> 'a1 -> (coq_World -> B.coq_Sub -> __ -> 'a1) -> coq_World ->
    coq_Acc -> 'a1

  val coq_Acc_rec :
    coq_World -> 'a1 -> (coq_World -> B.coq_Sub -> __ -> 'a1) -> coq_World ->
    coq_Acc -> 'a1

  val acc_trans :
    coq_World -> coq_World -> coq_World -> coq_Acc -> coq_Acc -> coq_Acc

  val sub_acc : coq_World -> coq_World -> coq_Acc -> B.coq_Sub

  type 'a coq_Box = coq_World -> coq_Acc -> 'a

  val acc_wnil_init : coq_World -> coq_Acc

  val acc_wlctx_valuation :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env ->
    coq_Acc

  val acc_snoc_right :
    coq_World -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_Acc

  val acc_cat_right :
    coq_World -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_Acc

  val acc_snoc_left :
    coq_World -> coq_World -> coq_Acc -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> B.coq_Term -> coq_Acc

  val acc_snoc_left' :
    coq_World -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> B.coq_Term ->
    coq_Acc

  val acc_cat_left :
    coq_World -> coq_World -> coq_Acc -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> B.coq_Sub -> coq_Acc

  val acc_formula_right : coq_World -> coq_Formula -> coq_Acc

  val acc_pathcondition_right : coq_World -> coq_PathCondition -> coq_Acc

  val acc_subst_right :
    coq_World -> lVar -> Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> B.coq_Term -> coq_Acc

  val acc_match_right :
    coq_World -> Coq_ty.coq_Ty -> B.coq_Term -> lVar B.coq_Pattern -> lVar
    B.coq_PatternCase -> coq_Acc

  val sub_matchvar_right :
    coq_World -> lVar -> Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> lVar B.coq_Pattern -> lVar
    B.coq_PatternCase -> B.coq_Sub

  val acc_matchvar_right :
    coq_World -> lVar -> Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> lVar B.coq_Pattern -> lVar
    B.coq_PatternCase -> coq_Acc

  val acc_triangular : coq_World -> coq_World -> coq_Tri -> coq_Acc

  val preorder_acc : (coq_World, coq_Acc) preOrder

  val coq_K :
    (('a1, 'a2) coq_Impl coq_Box, ('a1 coq_Box, 'a2 coq_Box) coq_Impl)
    coq_Impl coq_Valid

  val coq_T : ('a1 coq_Box, 'a1) coq_Impl coq_Valid

  val four : ('a1 coq_Box, 'a1 coq_Box coq_Box) coq_Impl coq_Valid

  val valid_box : 'a1 coq_Valid -> 'a1 coq_Box coq_Valid

  val fmap_box :
    ('a1, 'a2) coq_Impl coq_Valid -> ('a1 coq_Box, 'a2 coq_Box) coq_Impl
    coq_Valid

  val extend_box :
    ('a1 coq_Box, 'a2) coq_Impl coq_Valid -> ('a1 coq_Box, 'a2 coq_Box)
    coq_Impl coq_Valid

  val comp :
    (('a2, 'a3) coq_Impl, (('a1, 'a2) coq_Impl, ('a1, 'a3) coq_Impl)
    coq_Impl) coq_Impl coq_Valid

  module ModalNotations :
   sig
   end

  type 'a coq_Persistent = ('a, 'a coq_Box) coq_Impl coq_Valid

  val persist : 'a1 coq_Persistent -> ('a1, 'a1 coq_Box) coq_Impl coq_Valid

  val persistent_box : 'a1 coq_Box coq_Persistent

  val persistent_subst : 'a1 B.coq_Subst -> 'a1 coq_Persistent

  type 'a coq_Tm = 'a

  val bi_pred : coq_World -> bi

  type 't coq_InstPred =
  | MkInstPred

  val instpred_option : 'a1 coq_InstPred -> 'a1 B.coq_Option coq_InstPred

  val instpred_pair :
    'a1 coq_InstPred -> 'a2 coq_InstPred -> ('a1, 'a2) B.coq_Pair coq_InstPred

  val instpred_ctx_inst : 'a1 coq_InstPred -> 'a1 Coq_ctx.coq_Ctx coq_InstPred

  val instpred_inst_formula : coq_Formula coq_InstPred

  type coq_Solver =
    coq_World -> coq_PathCondition -> (coq_World, (coq_Tri,
    coq_PathCondition) prod) sigT option

  val solver_null : coq_Solver

  type coq_SolverUserOnly =
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> _UU1d477_ ->
    (Coq_ty.coq_Ty, B.coq_Term) Coq_env.coq_Env -> coq_PathCondition
    B.coq_Option

  val simplify_all :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_Formula
    -> coq_PathCondition -> coq_PathCondition option) -> coq_PathCondition ->
    coq_PathCondition -> coq_PathCondition option

  val solveruseronly_simplify_formula :
    coq_SolverUserOnly -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_Formula -> coq_PathCondition -> coq_PathCondition
    option

  val solveruseronly_to_solver : coq_SolverUserOnly -> coq_Solver

  val solver_compose : coq_Solver -> coq_Solver -> coq_Solver

  module DList :
   sig
    type coq_DList = { raw : (coq_PathCondition -> coq_PathCondition
                             B.coq_Option) }

    val raw :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DList
      -> coq_PathCondition -> coq_PathCondition B.coq_Option

    val instpred_dlist : coq_DList coq_InstPred

    val singleton :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_DList

    val run :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DList
      -> coq_PathCondition B.coq_Option

    val error :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DList

    val empty :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DList

    val cat :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DList
      -> coq_DList -> coq_DList
   end

  val solver : coq_Solver

  type coq_Message = { msg_function : string; msg_message : string;
                       msg_program_context : (pVar, Coq_ty.coq_Ty)
                                             Binding.coq_Binding
                                             Coq_ctx.coq_Ctx;
                       msg_localstore : B.coq_SStore; msg_heap : coq_SHeap;
                       msg_pathcondition : coq_PathCondition }

  val msg_function :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Message
    -> string

  val msg_message :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Message
    -> string

  val msg_program_context :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Message
    -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  val msg_localstore :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Message
    -> B.coq_SStore

  val msg_heap :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Message
    -> coq_SHeap

  val msg_pathcondition :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Message
    -> coq_PathCondition

  type coq_EMessage = { emsg_function : string; emsg_message : string;
                        emsg_program_context : (pVar, Coq_ty.coq_Ty)
                                               Binding.coq_Binding
                                               Coq_ctx.coq_Ctx;
                        emsg_localstore : (pVar, Coq_ty.coq_Ty, B.coq_ETerm)
                                          namedEnv;
                        emsg_heap : coq_EChunk list;
                        emsg_pathcondition : coq_EFormula list }

  val emsg_function : coq_EMessage -> string

  val emsg_message : coq_EMessage -> string

  val emsg_program_context :
    coq_EMessage -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  val emsg_localstore :
    coq_EMessage -> (pVar, Coq_ty.coq_Ty, B.coq_ETerm) namedEnv

  val emsg_heap : coq_EMessage -> coq_EChunk list

  val emsg_pathcondition : coq_EMessage -> coq_EFormula list

  val coq_EraseMessage : (coq_Message, coq_EMessage) B.coq_Erase

  val coq_SubstMessage : coq_Message B.coq_Subst

  val coq_SubstSUMessage :
    'a1 B.coq_SubstUniv -> ('a1, coq_Message) B.coq_SubstSU

  val coq_SubstLawsMessage : coq_Message B.coq_SubstLaws

  val coq_OccursCheckMessage : coq_Message B.coq_OccursCheck

  val coq_GenOccursCheckMessage :
    (B.coq_WeakensTo, coq_Message) B.coq_GenOccursCheck

  val coq_Error_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Message
    -> 'a1

  val coq_Error_rec :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Message
    -> 'a1

  val coq_Obligation_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    B.Coq_amsg.coq_AMessage -> coq_Formula -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env -> (__ -> 'a1) -> 'a1

  val coq_Obligation_rec :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    B.Coq_amsg.coq_AMessage -> coq_Formula -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env -> (__ -> 'a1) -> 'a1

  val coq_Debug_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 -> (__
    -> 'a2) -> 'a2

  val coq_Debug_rec :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 -> (__
    -> 'a2) -> 'a2

  module SymProp :
   sig
    type coq_SymProp =
    | Coq_angelic_binary of coq_SymProp * coq_SymProp
    | Coq_demonic_binary of coq_SymProp * coq_SymProp
    | Coq_error of B.Coq_amsg.coq_AMessage
    | Coq_block
    | Coq_assertk of coq_Formula * B.Coq_amsg.coq_AMessage * coq_SymProp
    | Coq_assumek of coq_Formula * coq_SymProp
    | Coq_angelicv of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding * coq_SymProp
    | Coq_demonicv of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding * coq_SymProp
    | Coq_assert_vareq of lVar * Coq_ty.coq_Ty
       * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
       * B.coq_Term * B.Coq_amsg.coq_AMessage * coq_SymProp
    | Coq_assume_vareq of lVar * Coq_ty.coq_Ty
       * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
       * B.coq_Term * coq_SymProp
    | Coq_pattern_match of Coq_ty.coq_Ty * B.coq_Term * lVar B.coq_Pattern
       * (lVar B.coq_PatternCase -> coq_SymProp)
    | Coq_pattern_match_var of lVar * Coq_ty.coq_Ty
       * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
       * lVar B.coq_Pattern * (lVar B.coq_PatternCase -> coq_SymProp)
    | Coq_debug of B.Coq_amsg.coq_AMessage * coq_SymProp

    val coq_SymProp_rect :
      ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SymProp -> 'a1 -> coq_SymProp -> 'a1 -> 'a1) -> ((lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SymProp ->
      'a1 -> coq_SymProp -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> B.Coq_amsg.coq_AMessage -> 'a1)
      -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1)
      -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> B.Coq_amsg.coq_AMessage -> coq_SymProp -> 'a1 -> 'a1) ->
      ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_SymProp -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding -> coq_SymProp -> 'a1 -> 'a1) -> ((lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> coq_SymProp -> 'a1 -> 'a1) ->
      ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar ->
      Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> B.coq_Term -> B.Coq_amsg.coq_AMessage -> coq_SymProp
      -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> lVar -> Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> B.coq_Term -> coq_SymProp -> 'a1
      -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
      -> Coq_ty.coq_Ty -> B.coq_Term -> lVar B.coq_Pattern -> (lVar
      B.coq_PatternCase -> coq_SymProp) -> (lVar B.coq_PatternCase -> 'a1) ->
      'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      lVar -> Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> lVar B.coq_Pattern -> (lVar B.coq_PatternCase ->
      coq_SymProp) -> (lVar B.coq_PatternCase -> 'a1) -> 'a1) -> ((lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.Coq_amsg.coq_AMessage -> coq_SymProp -> 'a1 -> 'a1) -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SymProp -> 'a1

    val coq_SymProp_rec :
      ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SymProp -> 'a1 -> coq_SymProp -> 'a1 -> 'a1) -> ((lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SymProp ->
      'a1 -> coq_SymProp -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> B.Coq_amsg.coq_AMessage -> 'a1)
      -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1)
      -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> B.Coq_amsg.coq_AMessage -> coq_SymProp -> 'a1 -> 'a1) ->
      ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_SymProp -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding -> coq_SymProp -> 'a1 -> 'a1) -> ((lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> coq_SymProp -> 'a1 -> 'a1) ->
      ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar ->
      Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> B.coq_Term -> B.Coq_amsg.coq_AMessage -> coq_SymProp
      -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> lVar -> Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> B.coq_Term -> coq_SymProp -> 'a1
      -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
      -> Coq_ty.coq_Ty -> B.coq_Term -> lVar B.coq_Pattern -> (lVar
      B.coq_PatternCase -> coq_SymProp) -> (lVar B.coq_PatternCase -> 'a1) ->
      'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      lVar -> Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> lVar B.coq_Pattern -> (lVar B.coq_PatternCase ->
      coq_SymProp) -> (lVar B.coq_PatternCase -> 'a1) -> 'a1) -> ((lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.Coq_amsg.coq_AMessage -> coq_SymProp -> 'a1 -> 'a1) -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SymProp -> 'a1

    val trunc :
      nat -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SymProp -> coq_SymProp

    val angelic_close0 :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SymProp ->
      coq_SymProp

    val demonic_close0 :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SymProp ->
      coq_SymProp

    val demonic_close :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SymProp -> coq_SymProp

    val angelic_list' :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SymProp -> ('a1 -> coq_SymProp) -> 'a1 B.coq_List -> coq_SymProp

    val angelic_list :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.Coq_amsg.coq_AMessage -> ('a1 -> coq_SymProp) -> 'a1 B.coq_List ->
      coq_SymProp

    val demonic_list' :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SymProp -> ('a1 -> coq_SymProp) -> 'a1 B.coq_List -> coq_SymProp

    val demonic_list :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1 ->
      coq_SymProp) -> 'a1 B.coq_List -> coq_SymProp

    val angelic_finite :
      ('a1, 'a1) relDecision -> 'a1 finite -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> B.Coq_amsg.coq_AMessage -> ('a1
      -> coq_SymProp) -> coq_SymProp

    val demonic_finite :
      ('a1, 'a1) relDecision -> 'a1 finite -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1 -> coq_SymProp) ->
      coq_SymProp

    val angelic_pattern_match :
      Coq_ty.coq_Ty -> lVar B.coq_Pattern -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> B.coq_Term -> (lVar
      B.coq_PatternCase -> coq_SymProp) -> coq_SymProp

    val angelic_pattern_match_var :
      Coq_ty.coq_Ty -> lVar B.coq_Pattern -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> (lVar B.coq_PatternCase ->
      coq_SymProp) -> coq_SymProp

    val demonic_pattern_match :
      Coq_ty.coq_Ty -> lVar B.coq_Pattern -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> B.coq_Term -> (lVar
      B.coq_PatternCase -> coq_SymProp) -> coq_SymProp

    val demonic_pattern_match_var :
      Coq_ty.coq_Ty -> lVar B.coq_Pattern -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> (lVar B.coq_PatternCase ->
      coq_SymProp) -> coq_SymProp

    val assume_pathcondition_without_solver' :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_PathCondition -> coq_SymProp -> coq_SymProp

    val assert_pathcondition_without_solver' :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.Coq_amsg.coq_AMessage -> coq_PathCondition -> coq_SymProp ->
      coq_SymProp

    val assume_pathcondition_without_solver :
      coq_World -> coq_PathCondition -> coq_SymProp -> coq_SymProp

    val assert_pathcondition_without_solver :
      coq_World -> B.Coq_amsg.coq_AMessage -> coq_PathCondition ->
      coq_SymProp -> coq_SymProp

    val assume_triangular :
      coq_World -> coq_World -> coq_Tri -> coq_SymProp -> coq_SymProp

    val assert_triangular :
      coq_World -> coq_World -> B.Coq_amsg.coq_AMessage -> coq_Tri ->
      (B.Coq_amsg.coq_AMessage -> coq_SymProp) -> coq_SymProp

    module Coq_notations :
     sig
     end

    module Statistics :
     sig
      val size :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_SymProp -> n

      type coq_Count = { block : n; error : n; debug : n }

      val block : coq_Count -> n

      val error : coq_Count -> n

      val debug : coq_Count -> n

      val empty : coq_Count

      val inc_block : coq_Count -> coq_Count

      val inc_error : coq_Count -> coq_Count

      val inc_debug : coq_Count -> coq_Count

      val count_nodes :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_SymProp -> coq_Count -> coq_Count

      val count_to_stats : coq_Count -> stats
     end
   end

  module Postprocessing :
   sig
    type ('m1, 'm2) coq_AngelicBinaryFailMsg = { angelic_binary_failmsg_left : 
                                                 'm1;
                                                 angelic_binary_failmsg_right : 
                                                 'm2 }

    val angelic_binary_failmsg_left :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, 'a2)
      coq_AngelicBinaryFailMsg -> 'a1

    val angelic_binary_failmsg_right :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, 'a2)
      coq_AngelicBinaryFailMsg -> 'a2

    val coq_SubstAngelicBinaryFailMsg :
      'a1 B.coq_Subst -> 'a2 B.coq_Subst -> ('a1, 'a2)
      coq_AngelicBinaryFailMsg B.coq_Subst

    val coq_SubstSUAngelicBinaryFailMsg :
      ('a1, 'a2) B.coq_SubstSU -> ('a1, 'a3) B.coq_SubstSU -> ('a1, ('a2,
      'a3) coq_AngelicBinaryFailMsg) B.coq_SubstSU

    val coq_SubstLawsAngelicBinaryFailMsg :
      'a1 B.coq_Subst -> 'a1 B.coq_SubstLaws -> 'a2 B.coq_Subst -> 'a2
      B.coq_SubstLaws -> ('a1, 'a2) coq_AngelicBinaryFailMsg B.coq_SubstLaws

    val coq_OccursCheckAngelicBinaryFailMsg :
      'a1 B.coq_OccursCheck -> 'a2 B.coq_OccursCheck -> ('a1, 'a2)
      coq_AngelicBinaryFailMsg B.coq_OccursCheck

    val coq_GenOccursCheckAngelicBinaryFailMsg :
      (B.coq_WeakensTo, 'a1) B.coq_SubstSU -> 'a1 B.coq_Subst ->
      (B.coq_WeakensTo, 'a2) B.coq_SubstSU -> 'a2 B.coq_Subst ->
      (B.coq_WeakensTo, 'a1) B.coq_GenOccursCheck -> (B.coq_WeakensTo, 'a2)
      B.coq_GenOccursCheck -> (B.coq_WeakensTo, ('a1, 'a2)
      coq_AngelicBinaryFailMsg) B.coq_GenOccursCheck

    type ('mE1, 'mE2) coq_EAngelicBinaryFailMsg =
    | MkEAngelicBinaryFailMsg of 'mE1 * 'mE2

    val coq_EAngelicBinaryFailMsg_rect :
      ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) coq_EAngelicBinaryFailMsg -> 'a3

    val coq_EAngelicBinaryFailMsg_rec :
      ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) coq_EAngelicBinaryFailMsg -> 'a3

    val coq_EraseAngelicBinaryFailMsg :
      ('a1, 'a2) B.coq_Erase -> ('a3, 'a4) B.coq_Erase -> (('a1, 'a3)
      coq_AngelicBinaryFailMsg, ('a2, 'a4) coq_EAngelicBinaryFailMsg)
      B.coq_Erase

    val angelic_binary_prune :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> SymProp.coq_SymProp -> SymProp.coq_SymProp

    val demonic_binary_prune :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> SymProp.coq_SymProp -> SymProp.coq_SymProp

    val assertk_prune :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> B.Coq_amsg.coq_AMessage -> SymProp.coq_SymProp ->
      SymProp.coq_SymProp

    val assumek_prune :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> SymProp.coq_SymProp -> SymProp.coq_SymProp

    val angelicv_prune :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> SymProp.coq_SymProp ->
      SymProp.coq_SymProp

    val demonicv_prune :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> SymProp.coq_SymProp ->
      SymProp.coq_SymProp

    val assume_vareq_prune :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar ->
      Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> B.coq_Term -> SymProp.coq_SymProp ->
      SymProp.coq_SymProp

    val assert_vareq_prune :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar ->
      Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> B.coq_Term -> B.Coq_amsg.coq_AMessage ->
      SymProp.coq_SymProp -> SymProp.coq_SymProp

    val prune :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> SymProp.coq_SymProp

    module SolveEvars :
     sig
      val assert_msgs_formulas :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (B.Coq_amsg.coq_AMessage, coq_Formula) B.coq_Pair Coq_ctx.coq_Ctx ->
        SymProp.coq_SymProp -> SymProp.coq_SymProp

      type coq_ECtx =
      | Coq_ectx of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
         * (B.Coq_amsg.coq_AMessage, coq_Formula) B.coq_Pair Coq_ctx.coq_Ctx

      val coq_ECtx_rect :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ((lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (B.Coq_amsg.coq_AMessage, coq_Formula) B.coq_Pair Coq_ctx.coq_Ctx ->
        'a1) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_ECtx -> 'a1

      val coq_ECtx_rec :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ((lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (B.Coq_amsg.coq_AMessage, coq_Formula) B.coq_Pair Coq_ctx.coq_Ctx ->
        'a1) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_ECtx -> 'a1

      val ectx_refl :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_ECtx

      val ectx_formula :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_ECtx ->
        B.Coq_amsg.coq_AMessage -> coq_Formula -> coq_ECtx

      val ectx_snoc :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_ECtx ->
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_ECtx

      val ectx_subst :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_ECtx ->
        lVar -> Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_In -> B.coq_Term -> coq_ECtx option

      val plug :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_ECtx ->
        SymProp.coq_SymProp -> SymProp.coq_SymProp

      val plug_msg :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_ECtx ->
        B.Coq_amsg.coq_AMessage -> B.Coq_amsg.coq_AMessage

      val push :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_ECtx ->
        SymProp.coq_SymProp -> SymProp.coq_SymProp
     end

    val solve_evars :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> SymProp.coq_SymProp

    module SolveUvars :
     sig
      val assume_pathcondition :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_PathCondition -> SymProp.coq_SymProp -> SymProp.coq_SymProp

      type coq_UCtx =
      | Coq_uctx of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
         * coq_PathCondition

      val coq_UCtx_rect :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ((lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_PathCondition -> 'a1) -> (lVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_UCtx -> 'a1

      val coq_UCtx_rec :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ((lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_PathCondition -> 'a1) -> (lVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_UCtx -> 'a1

      val uctx_refl :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_UCtx

      val uctx_formula :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_UCtx ->
        coq_Formula -> coq_UCtx

      val uctx_snoc :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_UCtx ->
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_UCtx

      val uctx_subst :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_UCtx ->
        lVar -> Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_In -> B.coq_Term -> coq_UCtx option

      val plug :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_UCtx ->
        SymProp.coq_SymProp -> SymProp.coq_SymProp

      val plug_error :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_UCtx ->
        B.Coq_amsg.coq_AMessage -> SymProp.coq_SymProp

      val push :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_UCtx ->
        SymProp.coq_SymProp -> SymProp.coq_SymProp
     end

    val solve_uvars :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> SymProp.coq_SymProp

    module Experimental :
     sig
      type coq_Ephemeral = (SolveEvars.coq_ECtx, SolveUvars.coq_UCtx) sum

      type coq_EProp =
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_Ephemeral -> SymProp.coq_SymProp

      val angelic_binary :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_EProp -> coq_EProp -> coq_EProp

      val angelicv :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding -> coq_EProp -> coq_EProp

      val demonic_binary :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_EProp -> coq_EProp -> coq_EProp

      val error :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        B.Coq_amsg.coq_AMessage -> coq_EProp
     end

    val weaken_symprop :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> B.coq_WeakensTo -> SymProp.coq_SymProp

    val coq_SubstSU_SymProp :
      (B.coq_WeakensTo, SymProp.coq_SymProp) B.coq_SubstSU

    type coq_UQSymProp = (B.coq_WeakensTo, SymProp.coq_SymProp) B.coq_Weakened

    val from_uqSymProp :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_UQSymProp -> SymProp.coq_SymProp

    val uq_angelic_binary :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_UQSymProp -> coq_UQSymProp -> coq_UQSymProp

    val uq_demonic_binary :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_UQSymProp -> coq_UQSymProp -> coq_UQSymProp

    val uq_error :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.Coq_amsg.coq_AMessage -> coq_UQSymProp

    val uq_block :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_UQSymProp

    val uq_assertk :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> B.Coq_amsg.coq_AMessage -> coq_UQSymProp -> coq_UQSymProp

    val uq_assumek :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_UQSymProp -> coq_UQSymProp

    val uq_angelicv :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> coq_UQSymProp -> coq_UQSymProp

    val uq_demonicv :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> coq_UQSymProp -> coq_UQSymProp

    val uq_assert_vareq :
      lVar -> Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> B.coq_Term -> B.Coq_amsg.coq_AMessage ->
      coq_UQSymProp -> coq_UQSymProp

    val uq_assume_vareq :
      lVar -> Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> B.coq_Term -> coq_UQSymProp -> coq_UQSymProp

    val uq_debug :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.Coq_amsg.coq_AMessage -> coq_UQSymProp -> coq_UQSymProp

    val to_uqSymProp :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> coq_UQSymProp

    val unquantify :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> SymProp.coq_SymProp

    val weakenWorld :
      coq_World -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
      -> B.coq_WeakensTo -> coq_World

    val weakenWorld_acc :
      coq_World -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
      -> B.coq_WeakensTo -> coq_Acc
   end

  val postprocess :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    SymProp.coq_SymProp -> SymProp.coq_SymProp

  val postprocess2 :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    SymProp.coq_SymProp -> SymProp.coq_SymProp

  module Erasure :
   sig
    type coq_ESymProp =
    | Coq_eangelic_binary of coq_ESymProp * coq_ESymProp
    | Coq_edemonic_binary of coq_ESymProp * coq_ESymProp
    | Coq_eerror of B.Coq_amsg.coq_EAMessage
    | Coq_eblock
    | Coq_eassertk of coq_EFormula * coq_ESymProp
    | Coq_eassumek of coq_EFormula * coq_ESymProp
    | Coq_eangelicv of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
       * coq_ESymProp
    | Coq_edemonicv of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
       * coq_ESymProp
    | Coq_eassert_vareq of lVar * Coq_ty.coq_Ty * nat * B.coq_ETerm
       * coq_ESymProp
    | Coq_eassume_vareq of lVar * Coq_ty.coq_Ty * nat * B.coq_ETerm
       * coq_ESymProp
    | Coq_epattern_match of Coq_ty.coq_Ty * B.coq_ETerm * lVar B.coq_Pattern
       * (lVar B.coq_PatternCase -> coq_ESymProp)
    | Coq_epattern_match_var of lVar * Coq_ty.coq_Ty * nat
       * lVar B.coq_Pattern * (lVar B.coq_PatternCase -> coq_ESymProp)
    | Coq_edebug of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
       * B.Coq_amsg.coq_AMessage * coq_ESymProp

    val coq_ESymProp_rect :
      (coq_ESymProp -> 'a1 -> coq_ESymProp -> 'a1 -> 'a1) -> (coq_ESymProp ->
      'a1 -> coq_ESymProp -> 'a1 -> 'a1) -> (B.Coq_amsg.coq_EAMessage -> 'a1)
      -> 'a1 -> (coq_EFormula -> coq_ESymProp -> 'a1 -> 'a1) -> (coq_EFormula
      -> coq_ESymProp -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding -> coq_ESymProp -> 'a1 -> 'a1) -> ((lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> coq_ESymProp -> 'a1 -> 'a1) ->
      (lVar -> Coq_ty.coq_Ty -> nat -> B.coq_ETerm -> coq_ESymProp -> 'a1 ->
      'a1) -> (lVar -> Coq_ty.coq_Ty -> nat -> B.coq_ETerm -> coq_ESymProp ->
      'a1 -> 'a1) -> (Coq_ty.coq_Ty -> B.coq_ETerm -> lVar B.coq_Pattern ->
      (lVar B.coq_PatternCase -> coq_ESymProp) -> (lVar B.coq_PatternCase ->
      'a1) -> 'a1) -> (lVar -> Coq_ty.coq_Ty -> nat -> lVar B.coq_Pattern ->
      (lVar B.coq_PatternCase -> coq_ESymProp) -> (lVar B.coq_PatternCase ->
      'a1) -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> B.Coq_amsg.coq_AMessage -> coq_ESymProp -> 'a1 ->
      'a1) -> coq_ESymProp -> 'a1

    val coq_ESymProp_rec :
      (coq_ESymProp -> 'a1 -> coq_ESymProp -> 'a1 -> 'a1) -> (coq_ESymProp ->
      'a1 -> coq_ESymProp -> 'a1 -> 'a1) -> (B.Coq_amsg.coq_EAMessage -> 'a1)
      -> 'a1 -> (coq_EFormula -> coq_ESymProp -> 'a1 -> 'a1) -> (coq_EFormula
      -> coq_ESymProp -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding -> coq_ESymProp -> 'a1 -> 'a1) -> ((lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> coq_ESymProp -> 'a1 -> 'a1) ->
      (lVar -> Coq_ty.coq_Ty -> nat -> B.coq_ETerm -> coq_ESymProp -> 'a1 ->
      'a1) -> (lVar -> Coq_ty.coq_Ty -> nat -> B.coq_ETerm -> coq_ESymProp ->
      'a1 -> 'a1) -> (Coq_ty.coq_Ty -> B.coq_ETerm -> lVar B.coq_Pattern ->
      (lVar B.coq_PatternCase -> coq_ESymProp) -> (lVar B.coq_PatternCase ->
      'a1) -> 'a1) -> (lVar -> Coq_ty.coq_Ty -> nat -> lVar B.coq_Pattern ->
      (lVar B.coq_PatternCase -> coq_ESymProp) -> (lVar B.coq_PatternCase ->
      'a1) -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> B.Coq_amsg.coq_AMessage -> coq_ESymProp -> 'a1 ->
      'a1) -> coq_ESymProp -> 'a1

    val erase_symprop :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> coq_ESymProp

    val erase_SymProp : (SymProp.coq_SymProp, coq_ESymProp) B.coq_Erase

    val erase_valuation :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ((lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env ->
      (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list

    val erase_Valuation :
      (((lVar, Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val)
      Coq_env.coq_Env, (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list) B.coq_Erase

    val inst_env' :
      (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list -> (Coq_ty.coq_Ty ->
      B.coq_ETerm -> Coq_ty.coq_Val option) -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx
      -> (Coq_ty.coq_Ty, B.coq_ETerm) Coq_env.coq_Env -> (Coq_ty.coq_Ty,
      Coq_ty.coq_Val) Coq_env.coq_Env option

    val inst_namedenv' :
      (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list -> (Coq_ty.coq_Ty ->
      B.coq_ETerm -> Coq_ty.coq_Val option) -> ('a1, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty,
      B.coq_ETerm) namedEnv -> ('a1, Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv
      option

    val inst_eterm :
      (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list -> Coq_ty.coq_Ty ->
      B.coq_ETerm -> Coq_ty.coq_Val option

    val inst_namedenv :
      (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list -> ('a1, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty,
      B.coq_ETerm) namedEnv -> ('a1, Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv
      option

    val inst_env :
      (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list -> Coq_ty.coq_Ty
      Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, B.coq_ETerm) Coq_env.coq_Env ->
      (Coq_ty.coq_Ty, Coq_ty.coq_Val) Coq_env.coq_Env option

    val inst_eformula :
      (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list -> coq_EFormula -> __ option

    val list_remove : 'a1 list -> nat -> 'a1 list

    module Coq_notations :
     sig
     end
   end

  module Coq_notations :
   sig
   end

  val modality_assuming : coq_World -> coq_World -> coq_Acc -> modality

  val modality_forgetting : coq_World -> coq_World -> coq_Acc -> modality

  module Coq_logicalrelation :
   sig
    type ('aT, 'a) coq_Rel = { coq_RSat : ('a -> ('aT, coq_Pred) coq_Impl
                                          coq_Valid) }

    val coq_RInst : ('a1, 'a2) B.coq_Inst -> ('a1, 'a2) coq_Rel

    val coq_RInstPropIff : 'a1 coq_InstPred -> ('a1, __) coq_Rel

    val coq_RBox : ('a1, 'a2) coq_Rel -> ('a1 coq_Box, 'a2) coq_Rel

    val coq_RImpl :
      ('a1, 'a2) coq_Rel -> ('a3, 'a4) coq_Rel -> (('a1, 'a3) coq_Impl, 'a2
      -> 'a4) coq_Rel

    val coq_RForall :
      ('a1 -> ('a2, 'a3) coq_Rel) -> (('a1, 'a2) coq_Forall, 'a1 -> 'a3)
      coq_Rel

    val coq_RVal : Coq_ty.coq_Ty -> (B.coq_Term, Coq_ty.coq_Val) coq_Rel

    val coq_RNEnv :
      ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (('a1,
      Coq_ty.coq_Ty, B.coq_Term) namedEnv, ('a1, Coq_ty.coq_Ty,
      Coq_ty.coq_Val) namedEnv) coq_Rel

    val coq_REnv :
      Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ((Coq_ty.coq_Ty, B.coq_Term)
      Coq_env.coq_Env, (Coq_ty.coq_Ty, Coq_ty.coq_Val) Coq_env.coq_Env)
      coq_Rel

    val coq_RUnit : (B.coq_Unit, unit0) coq_Rel

    val coq_RPathCondition : (coq_PathCondition, __) coq_Rel

    val coq_RFormula : (coq_Formula, __) coq_Rel

    val coq_RChunk : (coq_Chunk, coq_SCChunk) coq_Rel

    val coq_RMsg : ('a2, 'a3) coq_Rel -> (('a1, 'a2) coq_Impl, 'a3) coq_Rel

    val coq_RList : ('a1, 'a2) coq_Rel -> ('a1 list, 'a2 list) coq_Rel

    val coq_RHeap : (coq_SHeap, coq_SCHeap) coq_Rel

    val coq_RConst : ('a1 B.coq_Const, 'a1) coq_Rel

    val coq_RProd :
      ('a1, 'a2) coq_Rel -> ('a3, 'a4) coq_Rel -> (('a1, 'a3) prod, ('a2,
      'a4) prod) coq_Rel

    val coq_RMatchResult :
      Coq_ty.coq_Ty -> 'a1 B.coq_Pattern -> ('a1 B.coq_SMatchResult, 'a1
      B.coq_MatchResult) coq_Rel

    val coq_RIn :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In, Coq_ty.coq_Val) coq_Rel

    module Coq_notations :
     sig
     end
   end

  module RSolve :
   sig
   end

  module AutorewriteUnifLogic :
   sig
   end

  module LogicalSoundness :
   sig
    val coq_RProp : (SymProp.coq_SymProp, __) Coq_logicalrelation.coq_Rel
   end

  module Coq_asn :
   sig
    type coq_Assertion =
    | Coq_formula of coq_Formula
    | Coq_chunk of coq_Chunk
    | Coq_chunk_angelic of coq_Chunk
    | Coq_pattern_match of Coq_ty.coq_Ty * B.coq_Term * lVar B.coq_Pattern
       * (lVar B.coq_PatternCase -> coq_Assertion)
    | Coq_sep of coq_Assertion * coq_Assertion
    | Coq_or of coq_Assertion * coq_Assertion
    | Coq_exist of lVar * Coq_ty.coq_Ty * coq_Assertion
    | Coq_debug

    val coq_Assertion_rect :
      ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> coq_Chunk -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Chunk -> 'a1) -> ((lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
      B.coq_Term -> lVar B.coq_Pattern -> (lVar B.coq_PatternCase ->
      coq_Assertion) -> (lVar B.coq_PatternCase -> 'a1) -> 'a1) -> ((lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Assertion ->
      'a1 -> coq_Assertion -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Assertion -> 'a1 ->
      coq_Assertion -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar -> Coq_ty.coq_Ty ->
      coq_Assertion -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1) -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Assertion -> 'a1

    val coq_Assertion_rec :
      ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> coq_Chunk -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Chunk -> 'a1) -> ((lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
      B.coq_Term -> lVar B.coq_Pattern -> (lVar B.coq_PatternCase ->
      coq_Assertion) -> (lVar B.coq_PatternCase -> 'a1) -> 'a1) -> ((lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Assertion ->
      'a1 -> coq_Assertion -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Assertion -> 'a1 ->
      coq_Assertion -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar -> Coq_ty.coq_Ty ->
      coq_Assertion -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1) -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Assertion -> 'a1

    val match_bool :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> B.coq_Term
      -> coq_Assertion -> coq_Assertion -> coq_Assertion

    val match_enum :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.enumi -> B.coq_Term -> (Coq_ty.enumt -> coq_Assertion) ->
      coq_Assertion

    val match_sum :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> B.coq_Term -> lVar -> coq_Assertion
      -> lVar -> coq_Assertion -> coq_Assertion

    val match_list :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> B.coq_Term -> coq_Assertion -> lVar -> lVar ->
      coq_Assertion -> coq_Assertion

    val match_prod :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> B.coq_Term -> lVar -> lVar ->
      coq_Assertion -> coq_Assertion

    val match_tuple :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> B.coq_Term -> lVar
      B.coq_TuplePat -> coq_Assertion -> coq_Assertion

    val match_record :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.recordi -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> B.coq_Term -> lVar B.coq_RecordPat -> coq_Assertion
      -> coq_Assertion

    val match_union_alt :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.unioni -> B.coq_Term -> (Coq_ty.unionk -> (lVar, coq_Assertion)
      B.coq_Alternative) -> coq_Assertion

    val exs :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Assertion ->
      coq_Assertion

    val sub_assertion : coq_Assertion B.coq_Subst

    val coq_OccursCheckAssertion : coq_Assertion B.coq_OccursCheck

    val is_pure :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Assertion -> bool

    val interpret :
      bi -> coq_PredicateDef -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> coq_Assertion -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env -> __

    module Coq_notations :
     sig
     end
   end

  type coq_SepContract = { sep_contract_logic_variables : (lVar,
                                                          Coq_ty.coq_Ty)
                                                          Binding.coq_Binding
                                                          Coq_ctx.coq_Ctx;
                           sep_contract_localstore : B.coq_SStore;
                           sep_contract_precondition : Coq_asn.coq_Assertion;
                           sep_contract_result : lVar;
                           sep_contract_postcondition : Coq_asn.coq_Assertion }

  val sep_contract_logic_variables :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContract -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx

  val sep_contract_localstore :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContract -> B.coq_SStore

  val sep_contract_precondition :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContract -> Coq_asn.coq_Assertion

  val sep_contract_result :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContract -> lVar

  val sep_contract_postcondition :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContract -> Coq_asn.coq_Assertion

  type coq_Lemma = { lemma_logic_variables : (lVar, Coq_ty.coq_Ty)
                                             Binding.coq_Binding
                                             Coq_ctx.coq_Ctx;
                     lemma_patterns : B.coq_SStore;
                     lemma_precondition : Coq_asn.coq_Assertion;
                     lemma_postcondition : Coq_asn.coq_Assertion }

  val lemma_logic_variables :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Lemma ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  val lemma_patterns :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Lemma ->
    B.coq_SStore

  val lemma_precondition :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Lemma ->
    Coq_asn.coq_Assertion

  val lemma_postcondition :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Lemma ->
    Coq_asn.coq_Assertion

  val lint_assertion :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> Coq_asn.coq_Assertion -> bool

  val lint_contract :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContract -> bool

  val lint_lemma :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Lemma ->
    bool

  val sep_contract_pun_logvars :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  type coq_SepContractPun = { sep_contract_pun_logic_variables : (lVar,
                                                                 Coq_ty.coq_Ty)
                                                                 Binding.coq_Binding
                                                                 Coq_ctx.coq_Ctx;
                              sep_contract_pun_precondition : Coq_asn.coq_Assertion;
                              sep_contract_pun_result : lVar;
                              sep_contract_pun_postcondition : Coq_asn.coq_Assertion }

  val sep_contract_pun_logic_variables :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContractPun -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx

  val sep_contract_pun_precondition :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContractPun -> Coq_asn.coq_Assertion

  val sep_contract_pun_result :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContractPun -> lVar

  val sep_contract_pun_postcondition :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContractPun -> Coq_asn.coq_Assertion

  val sep_contract_pun_to_sep_contract :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContractPun -> coq_SepContract

  val inst_contract_localstore :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContract -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env -> (pVar,
    Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv

  val interpret_contract_precondition :
    bi -> coq_PredicateDef -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> coq_SepContract -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env -> __

  val interpret_contract_postcondition :
    bi -> coq_PredicateDef -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> coq_SepContract -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env ->
    Coq_ty.coq_Val -> __

  module GenericSolver :
   sig
    val simplify_bool :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> B.coq_Term
      -> DList.coq_DList

    val simplify_bool_neg :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> B.coq_Term
      -> DList.coq_DList

    val simplify_eqb :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_eq_binop_default_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      B.coq_Term -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_unop_default_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> B.coq_Term ->
      Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_binop_and_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> B.coq_Term
      -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_binop_or_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> B.coq_Term
      -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_unop_not_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> B.coq_Term
      -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_binop_relop_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> B.coq_Term -> B.coq_Term ->
      Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_binop_pair_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList) ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term ->
      Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_binop_cons_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList) ->
      Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList

    val simplify_eq_binop_bvapp_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList) ->
      nat -> nat -> B.coq_Term -> B.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList

    val simplify_eq_binop_bvcons_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList) ->
      nat -> B.coq_Term -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_binop_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList) ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      B.coq_Term -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_unop_inl_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList) ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList

    val simplify_eq_unop_inr_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList) ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList

    val simplify_eq_unop_neg_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList) ->
      B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_unop_signed_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList) ->
      nat -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_unop_unsigned_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList) ->
      nat -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_unop_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList) ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> B.coq_Term ->
      Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_tuple_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList) ->
      Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, B.coq_Term)
      Coq_env.coq_Env -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_union_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList) ->
      Coq_ty.unioni -> Coq_ty.unionk -> B.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList

    val simplify_eq_record_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList) ->
      Coq_ty.recordi -> (Coq_ty.recordf, Coq_ty.coq_Ty, B.coq_Term) namedEnv
      -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> B.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_binop_default :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      B.coq_Term -> B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_eq_binop_minus :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> B.coq_Term
      -> B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_eq_binop_times :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> B.coq_Term
      -> B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_eq_unop_default :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> B.coq_Term ->
      B.coq_Term -> DList.coq_DList

    val simplify_eq_binop_plus :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) ->
      B.coq_Term -> B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_eq_binop_and :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> B.coq_Term
      -> B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_eq_binop_or :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> B.coq_Term
      -> B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_eq_binop_pair :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term ->
      B.coq_Term -> DList.coq_DList

    val simplify_eq_binop_cons :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) ->
      Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> B.coq_Term ->
      DList.coq_DList

    val simplify_eq_binop_append :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) ->
      Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> B.coq_Term ->
      DList.coq_DList

    val simplify_eq_binop_bvapp' :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) -> nat
      -> nat -> B.coq_Term -> B.coq_Term -> nat -> B.coq_Term ->
      DList.coq_DList

    val simplify_eq_binop_bvapp :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) -> nat
      -> nat -> B.coq_Term -> B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_eq_binop_bvcons' :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) -> nat
      -> B.coq_Term -> B.coq_Term -> nat -> B.coq_Term -> DList.coq_DList

    val simplify_eq_binop_bvcons :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) -> nat
      -> B.coq_Term -> B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_eq_relop :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> B.coq_Term -> B.coq_Term ->
      B.coq_Term -> DList.coq_DList

    val simplify_eq_binop :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      B.coq_Term -> B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_eq_unop_inl :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term ->
      DList.coq_DList

    val simplify_eq_unop_inr :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term ->
      DList.coq_DList

    val simplify_eq_unop_get_slice_int :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_eq_unop_signed :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) -> nat
      -> B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_eq_unop :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> B.coq_Term ->
      B.coq_Term -> DList.coq_DList

    val formula_eqs_ctx :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) ->
      Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, B.coq_Term)
      Coq_env.coq_Env -> (Coq_ty.coq_Ty, B.coq_Term) Coq_env.coq_Env ->
      DList.coq_DList

    val formula_eqs_nctx :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) -> ('a1,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1,
      Coq_ty.coq_Ty, B.coq_Term) namedEnv -> ('a1, Coq_ty.coq_Ty, B.coq_Term)
      namedEnv -> DList.coq_DList

    val simplify_eq_tuple :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) ->
      Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, B.coq_Term)
      Coq_env.coq_Env -> B.coq_Term -> DList.coq_DList

    val simplify_eq_record :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) ->
      Coq_ty.recordi -> (Coq_ty.recordf, Coq_ty.coq_Ty, B.coq_Term) namedEnv
      -> B.coq_Term -> DList.coq_DList

    val simplify_eq_union :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList) ->
      Coq_ty.unioni -> Coq_ty.unionk -> B.coq_Term -> B.coq_Term ->
      DList.coq_DList

    val simplify_eq :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_relopb :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> B.coq_Term -> B.coq_Term ->
      DList.coq_DList

    val peval_formula_le' :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> B.coq_Term
      -> coq_Formula

    val peval_formula_le :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> B.coq_Term
      -> B.coq_Term -> coq_Formula

    val peval_formula_lt :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> B.coq_Term
      -> B.coq_Term -> coq_Formula

    val peval_formula_relop_neg :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> B.coq_Term -> B.coq_Term ->
      coq_Formula

    val simplify_le :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> B.coq_Term
      -> B.coq_Term -> DList.coq_DList

    val simplify_bvule :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_bvult :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      B.coq_Term -> B.coq_Term -> DList.coq_DList

    val simplify_lt :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> B.coq_Term
      -> B.coq_Term -> DList.coq_DList

    val simplify_relop :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> B.coq_Term -> B.coq_Term ->
      DList.coq_DList

    val smart_and :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_Formula -> coq_Formula

    val coq_PathCondition_to_Formula :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_PathCondition -> coq_Formula

    val coq_PathCondition_to_DList :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_PathCondition -> DList.coq_DList

    val simplify_formula :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> DList.coq_DList

    val simplify_pathcondition :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_PathCondition -> DList.coq_DList

    val occurs_check_lt :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty -> B.coq_Term ->
      B.coq_Term option

    val try_unify_bool :
      coq_World -> B.coq_Term -> (coq_World, coq_Tri) sigT option

    val try_unify_eq :
      coq_World -> Coq_ty.coq_Ty -> B.coq_Term -> B.coq_Term -> (coq_World,
      coq_Tri) sigT option

    val try_unify_formula :
      coq_World -> coq_Formula -> (coq_World, coq_Tri) sigT option

    val unify_formula :
      coq_World -> coq_Formula -> (coq_World, (coq_Tri, coq_PathCondition)
      prod) sigT

    val unify_pathcondition :
      coq_World -> coq_PathCondition -> (coq_World, (coq_Tri,
      coq_PathCondition) prod) sigT

    val formula_eqb_clause_3 :
      ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_Formula -> bool) -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> _UU1d477_ -> (Coq_ty.coq_Ty,
      B.coq_Term) Coq_env.coq_Env -> _UU1d477_ -> sumbool -> (Coq_ty.coq_Ty,
      B.coq_Term) Coq_env.coq_Env -> bool

    val formula_eqb_clause_2 :
      ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_Formula -> bool) -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
      Coq_bop.coq_RelOp -> B.coq_Term -> B.coq_Term -> Coq_ty.coq_Ty ->
      sumbool -> Coq_bop.coq_RelOp -> B.coq_Term -> B.coq_Term -> bool

    val formula_eqb :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_Formula -> bool

    val smart_or :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_Formula -> coq_Formula

    val formula_simplifies :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_Formula -> coq_Formula option

    val assumption_formula :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_PathCondition -> coq_Formula -> coq_PathCondition ->
      coq_PathCondition

    val assumption_pathcondition :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_PathCondition -> coq_PathCondition -> coq_PathCondition ->
      coq_PathCondition

    val solver_generic : coq_Solver
   end

  val combined_solver : coq_Solver

  module CPureSpec :
   sig
    module Coq_notations :
     sig
     end
   end

  module CHeapSpec :
   sig
    module Coq_notations :
     sig
     end
   end

  module CStatistics :
   sig
    type coq_PropShape =
    | Coq_psfork of coq_PropShape * coq_PropShape
    | Coq_psquant of coq_PropShape
    | Coq_pspruned
    | Coq_psfinish
    | Coq_psother

    val coq_PropShape_rect :
      (coq_PropShape -> 'a1 -> coq_PropShape -> 'a1 -> 'a1) -> (coq_PropShape
      -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> coq_PropShape -> 'a1

    val coq_PropShape_rec :
      (coq_PropShape -> 'a1 -> coq_PropShape -> 'a1 -> 'a1) -> (coq_PropShape
      -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> coq_PropShape -> 'a1

    val shape_to_stats : coq_PropShape -> stats

    type coq_ShallowStats = stats

    val stats : coq_ShallowStats -> stats

    val stats_true : coq_ShallowStats

    val stats_false : coq_ShallowStats

    val stats_finish : coq_ShallowStats

    val stats_true' : coq_ShallowStats

    val stats_false' : coq_ShallowStats

    val stats_eq : 'a1 -> 'a1 -> coq_ShallowStats

    val stats_zle : z -> z -> coq_ShallowStats

    val stats_and : coq_ShallowStats -> coq_ShallowStats -> coq_ShallowStats

    val stats_or : coq_ShallowStats -> coq_ShallowStats -> coq_ShallowStats

    val stats_impl : coq_ShallowStats -> coq_ShallowStats -> coq_ShallowStats

    val undefined : 'a1

    val stats_forall : ('a1 -> coq_ShallowStats) -> coq_ShallowStats

    val stats_exists : ('a1 -> coq_ShallowStats) -> coq_ShallowStats
   end

  type coq_DebugAsn = { debug_asn_pathcondition : coq_PathCondition;
                        debug_asn_heap : coq_SHeap }

  val debug_asn_pathcondition :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DebugAsn
    -> coq_PathCondition

  val debug_asn_heap :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DebugAsn
    -> coq_SHeap

  val coq_SubstDebugAsn : coq_DebugAsn B.coq_Subst

  val coq_SubstSUDebugAsn : (B.coq_WeakensTo, coq_DebugAsn) B.coq_SubstSU

  val coq_SubstLawsDebugAsn : coq_DebugAsn B.coq_SubstLaws

  val coq_OccursCheckDebugAsn : coq_DebugAsn B.coq_OccursCheck

  type coq_DebugConsumeChunk = { debug_consume_chunk_pathcondition : 
                                 coq_PathCondition;
                                 debug_consume_chunk_heap : coq_SHeap;
                                 debug_consume_chunk_chunk : coq_Chunk }

  val debug_consume_chunk_pathcondition :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugConsumeChunk -> coq_PathCondition

  val debug_consume_chunk_heap :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugConsumeChunk -> coq_SHeap

  val debug_consume_chunk_chunk :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugConsumeChunk -> coq_Chunk

  type coq_EDebugConsumeChunk = { edebug_consume_chunk_pathcondition : 
                                  coq_EFormula list;
                                  edebug_consume_chunk_heap : coq_EChunk list;
                                  edebug_consume_chunk_chunk : coq_EChunk }

  val edebug_consume_chunk_pathcondition :
    coq_EDebugConsumeChunk -> coq_EFormula list

  val edebug_consume_chunk_heap : coq_EDebugConsumeChunk -> coq_EChunk list

  val edebug_consume_chunk_chunk : coq_EDebugConsumeChunk -> coq_EChunk

  val coq_Erase_DebugConsumeChunk :
    (coq_DebugConsumeChunk, coq_EDebugConsumeChunk) B.coq_Erase

  val coq_SubstDebugConsumeChunk : coq_DebugConsumeChunk B.coq_Subst

  val coq_SubstSUDebugConsumeChunk :
    'a1 B.coq_SubstUniv -> ('a1, coq_DebugConsumeChunk) B.coq_SubstSU

  val coq_SubstLawsDebugConsumeChunk : coq_DebugConsumeChunk B.coq_SubstLaws

  val coq_OccursCheckDebugConsumeChunk :
    coq_DebugConsumeChunk B.coq_OccursCheck

  type coq_DebugReadRegister = { debug_read_register_pathcondition : 
                                 coq_PathCondition;
                                 debug_read_register_heap : coq_SHeap;
                                 debug_read_register_type : Coq_ty.coq_Ty;
                                 debug_read_register_register : B._UU1d479__UU1d46c__UU1d46e_ }

  val debug_read_register_pathcondition :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugReadRegister -> coq_PathCondition

  val debug_read_register_heap :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugReadRegister -> coq_SHeap

  val debug_read_register_type :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugReadRegister -> Coq_ty.coq_Ty

  val debug_read_register_register :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugReadRegister -> B._UU1d479__UU1d46c__UU1d46e_

  type coq_EDebugReadRegister = { edebug_read_register_pathcondition : 
                                  coq_EFormula list;
                                  edebug_read_register_heap : coq_EChunk list;
                                  edebug_read_register_type : Coq_ty.coq_Ty;
                                  edebug_read_register_register : B._UU1d479__UU1d46c__UU1d46e_ }

  val edebug_read_register_pathcondition :
    coq_EDebugReadRegister -> coq_EFormula list

  val edebug_read_register_heap : coq_EDebugReadRegister -> coq_EChunk list

  val edebug_read_register_type : coq_EDebugReadRegister -> Coq_ty.coq_Ty

  val edebug_read_register_register :
    coq_EDebugReadRegister -> B._UU1d479__UU1d46c__UU1d46e_

  val coq_EraseDebugReadRegister :
    (coq_DebugReadRegister, coq_EDebugReadRegister) B.coq_Erase

  val coq_SubstDebugReadRegister : coq_DebugReadRegister B.coq_Subst

  val coq_SubstSUDebugReadRegister :
    'a1 B.coq_SubstUniv -> ('a1, coq_DebugReadRegister) B.coq_SubstSU

  val coq_SubstLawsDebugReadRegister : coq_DebugReadRegister B.coq_SubstLaws

  val coq_OccursCheckDebugReadRegister :
    coq_DebugReadRegister B.coq_OccursCheck

  type coq_DebugWriteRegister = { debug_write_register_pathcondition : 
                                  coq_PathCondition;
                                  debug_write_register_heap : coq_SHeap;
                                  debug_write_register_type : Coq_ty.coq_Ty;
                                  debug_write_register_register : B._UU1d479__UU1d46c__UU1d46e_;
                                  debug_write_register_value : B.coq_Term }

  val debug_write_register_pathcondition :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugWriteRegister -> coq_PathCondition

  val debug_write_register_heap :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugWriteRegister -> coq_SHeap

  val debug_write_register_type :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugWriteRegister -> Coq_ty.coq_Ty

  val debug_write_register_register :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugWriteRegister -> B._UU1d479__UU1d46c__UU1d46e_

  val debug_write_register_value :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugWriteRegister -> B.coq_Term

  type coq_EDebugWriteRegister = { edebug_write_register_pathcondition : 
                                   coq_EFormula list;
                                   edebug_write_register_heap : coq_EChunk
                                                                list;
                                   edebug_write_register_type : Coq_ty.coq_Ty;
                                   edebug_write_register_register : B._UU1d479__UU1d46c__UU1d46e_;
                                   edebug_write_register_value : B.coq_ETerm }

  val edebug_write_register_pathcondition :
    coq_EDebugWriteRegister -> coq_EFormula list

  val edebug_write_register_heap : coq_EDebugWriteRegister -> coq_EChunk list

  val edebug_write_register_type : coq_EDebugWriteRegister -> Coq_ty.coq_Ty

  val edebug_write_register_register :
    coq_EDebugWriteRegister -> B._UU1d479__UU1d46c__UU1d46e_

  val edebug_write_register_value : coq_EDebugWriteRegister -> B.coq_ETerm

  val coq_EraseDebugWriteRegister :
    (coq_DebugWriteRegister, coq_EDebugWriteRegister) B.coq_Erase

  val coq_SubstDebugWriteRegister : coq_DebugWriteRegister B.coq_Subst

  val coq_SubstSUDebugWriteRegister :
    'a1 B.coq_SubstUniv -> ('a1, coq_DebugWriteRegister) B.coq_SubstSU

  val coq_SubstLawsDebugWriteRegister : coq_DebugWriteRegister B.coq_SubstLaws

  val coq_OccursCheckDebugWriteRegister :
    coq_DebugWriteRegister B.coq_OccursCheck

  type coq_DebugString = { debug_string_pathcondition : coq_PathCondition;
                           debug_string_message : string }

  val debug_string_pathcondition :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugString -> coq_PathCondition

  val debug_string_message :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugString -> string

  type coq_EDebugString = { edebug_string_pathcondition : coq_EFormula list;
                            edebug_string_message : string }

  val edebug_string_pathcondition : coq_EDebugString -> coq_EFormula list

  val edebug_string_message : coq_EDebugString -> string

  val coq_EraseDebugString : (coq_DebugString, coq_EDebugString) B.coq_Erase

  val coq_SubstDebugString : coq_DebugString B.coq_Subst

  val coq_SubstSUDebugString :
    (B.coq_WeakensTo, coq_DebugString) B.coq_SubstSU

  val coq_SubstLawsDebugString : coq_DebugString B.coq_SubstLaws

  val coq_OccursCheckDebugString : coq_DebugString B.coq_OccursCheck

  type coq_DebugAssertFormula = { debug_assert_formula_pathcondition : 
                                  coq_PathCondition;
                                  debug_assert_formula_heap : coq_SHeap;
                                  debug_assert_formula_formula : coq_Formula }

  val debug_assert_formula_pathcondition :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugAssertFormula -> coq_PathCondition

  val debug_assert_formula_heap :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugAssertFormula -> coq_SHeap

  val debug_assert_formula_formula :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugAssertFormula -> coq_Formula

  val coq_SubstDebugAssertFormula : coq_DebugAssertFormula B.coq_Subst

  val coq_SubstSUDebugAssertFormula :
    (B.coq_WeakensTo, coq_DebugAssertFormula) B.coq_SubstSU

  val coq_SubstLawsDebugAssertFormula : coq_DebugAssertFormula B.coq_SubstLaws

  val coq_OccursCheckDebugAssertFormula :
    coq_DebugAssertFormula B.coq_OccursCheck

  type 'a coq_SPureSpec =
    (('a, SymProp.coq_SymProp) coq_Impl coq_Box, SymProp.coq_SymProp) coq_Impl

  module SPureSpec :
   sig
    val run :
      (B.coq_Unit coq_SPureSpec, SymProp.coq_SymProp) coq_Impl coq_Valid

    val pure : ('a1, 'a1 coq_SPureSpec) coq_Impl coq_Valid

    val bind :
      ('a1 coq_SPureSpec, (('a1, 'a2 coq_SPureSpec) coq_Impl coq_Box, 'a2
      coq_SPureSpec) coq_Impl) coq_Impl coq_Valid

    module Coq_notations :
     sig
     end

    val block : 'a1 coq_SPureSpec coq_Valid

    val error :
      (B.Coq_amsg.coq_AMessage, 'a1 coq_SPureSpec) coq_Impl coq_Valid

    val angelic :
      lVar option -> (Coq_ty.coq_Ty, B.coq_Term coq_SPureSpec) coq_Forall
      coq_Valid

    val demonic :
      lVar option -> (Coq_ty.coq_Ty, B.coq_Term coq_SPureSpec) coq_Forall
      coq_Valid

    val angelic_ctx :
      ('a1 -> lVar) -> (('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx, ('a1, Coq_ty.coq_Ty, B.coq_Term) namedEnv
      coq_SPureSpec) coq_Forall coq_Valid

    val demonic_ctx :
      ('a1 -> lVar) -> (('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx, ('a1, Coq_ty.coq_Ty, B.coq_Term) namedEnv
      coq_SPureSpec) coq_Forall coq_Valid

    val assert_pathcondition :
      (B.Coq_amsg.coq_AMessage, (coq_PathCondition, B.coq_Unit coq_SPureSpec)
      coq_Impl) coq_Impl coq_Valid

    val assume_pathcondition :
      (coq_PathCondition, B.coq_Unit coq_SPureSpec) coq_Impl coq_Valid

    val assert_formula :
      (B.Coq_amsg.coq_AMessage, (coq_Formula, B.coq_Unit coq_SPureSpec)
      coq_Impl) coq_Impl coq_Valid

    val assume_formula :
      (coq_Formula, B.coq_Unit coq_SPureSpec) coq_Impl coq_Valid

    val angelic_binary :
      ('a1 coq_SPureSpec, ('a1 coq_SPureSpec, 'a1 coq_SPureSpec) coq_Impl)
      coq_Impl coq_Valid

    val demonic_binary :
      ('a1 coq_SPureSpec, ('a1 coq_SPureSpec, 'a1 coq_SPureSpec) coq_Impl)
      coq_Impl coq_Valid

    val angelic_list' :
      ('a1, ('a1 list, 'a1 coq_SPureSpec) coq_Impl) coq_Impl coq_Valid

    val angelic_list :
      (B.Coq_amsg.coq_AMessage, ('a1 list, 'a1 coq_SPureSpec) coq_Impl)
      coq_Impl coq_Valid

    val demonic_list' :
      ('a1, ('a1 list, 'a1 coq_SPureSpec) coq_Impl) coq_Impl coq_Valid

    val demonic_list : ('a1 list, 'a1 coq_SPureSpec) coq_Impl coq_Valid

    val angelic_finite :
      ('a1, 'a1) relDecision -> 'a1 finite -> (B.Coq_amsg.coq_AMessage, 'a1
      B.coq_Const coq_SPureSpec) coq_Impl coq_Valid

    val demonic_finite :
      ('a1, 'a1) relDecision -> 'a1 finite -> 'a1 B.coq_Const coq_SPureSpec
      coq_Valid

    val angelic_pattern_match' :
      ('a1 -> lVar) -> Coq_ty.coq_Ty -> 'a1 B.coq_Pattern ->
      (B.Coq_amsg.coq_AMessage, (B.coq_Term, 'a1 B.coq_SMatchResult
      coq_SPureSpec) coq_Impl) coq_Impl coq_Valid

    val angelic_pattern_match :
      ('a1 -> lVar) -> Coq_ty.coq_Ty -> 'a1 B.coq_Pattern ->
      (B.Coq_amsg.coq_AMessage, (B.coq_Term, 'a1 B.coq_SMatchResult
      coq_SPureSpec) coq_Impl) coq_Impl coq_Valid

    val demonic_pattern_match' :
      ('a1 -> lVar) -> Coq_ty.coq_Ty -> 'a1 B.coq_Pattern -> (B.coq_Term, 'a1
      B.coq_SMatchResult coq_SPureSpec) coq_Impl coq_Valid

    val demonic_pattern_match :
      ('a1 -> lVar) -> Coq_ty.coq_Ty -> 'a1 B.coq_Pattern -> (B.coq_Term, 'a1
      B.coq_SMatchResult coq_SPureSpec) coq_Impl coq_Valid

    val new_pattern_match_regular :
      ('a1 -> lVar) -> Coq_ty.coq_Ty -> 'a1 B.coq_Pattern -> (B.coq_Term, 'a1
      B.coq_SMatchResult coq_SPureSpec) coq_Impl coq_Valid

    val new_pattern_match_var :
      ('a1 -> lVar) -> Coq_ty.coq_Ty -> lVar -> 'a1 B.coq_Pattern -> ((lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In, 'a1
      B.coq_SMatchResult coq_SPureSpec) coq_Impl coq_Valid

    val new_pattern_match' :
      ('a1 -> lVar) -> Coq_ty.coq_Ty -> 'a1 B.coq_Pattern -> (B.coq_Term, 'a1
      B.coq_SMatchResult coq_SPureSpec) coq_Impl coq_Valid

    val new_pattern_match :
      ('a1 -> lVar) -> Coq_ty.coq_Ty -> 'a1 B.coq_Pattern -> (B.coq_Term, 'a1
      B.coq_SMatchResult coq_SPureSpec) coq_Impl coq_Valid

    val debug :
      (B.Coq_amsg.coq_AMessage, ('a1 coq_SPureSpec, 'a1 coq_SPureSpec)
      coq_Impl) coq_Impl coq_Valid

    val assert_eq_env :
      (Coq_ty.coq_Ty Coq_ctx.coq_Ctx, (B.Coq_amsg.coq_AMessage,
      ((Coq_ty.coq_Ty, B.coq_Term) Coq_env.coq_Env, ((Coq_ty.coq_Ty,
      B.coq_Term) Coq_env.coq_Env, B.coq_Unit coq_SPureSpec) coq_Impl)
      coq_Impl) coq_Impl) coq_Forall coq_Valid

    val assert_eq_nenv :
      (('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx,
      (B.Coq_amsg.coq_AMessage, (('a1, Coq_ty.coq_Ty, B.coq_Term) namedEnv,
      (('a1, Coq_ty.coq_Ty, B.coq_Term) namedEnv, B.coq_Unit coq_SPureSpec)
      coq_Impl) coq_Impl) coq_Impl) coq_Forall coq_Valid

    val assert_eq_chunk :
      (B.Coq_amsg.coq_AMessage, (coq_Chunk, (coq_Chunk, B.coq_Unit
      coq_SPureSpec coq_Box) coq_Impl) coq_Impl) coq_Impl coq_Valid

    val replay_aux :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> (B.coq_Sub, B.coq_Unit coq_SPureSpec) coq_Impl
      coq_Valid

    val replay : (SymProp.coq_SymProp, SymProp.coq_SymProp) coq_Impl coq_Valid

    val produce_chunk :
      (coq_Chunk, (coq_SHeap, coq_SHeap coq_SPureSpec) coq_Impl) coq_Impl
      coq_Valid

    val consume_chunk :
      (coq_Chunk, (coq_SHeap, coq_SHeap coq_SPureSpec) coq_Impl) coq_Impl
      coq_Valid

    val consume_chunk_angelic :
      (coq_Chunk, (coq_SHeap, coq_SHeap coq_SPureSpec) coq_Impl) coq_Impl
      coq_Valid

    val read_register :
      Coq_ty.coq_Ty -> B._UU1d479__UU1d46c__UU1d46e_ -> (coq_SHeap,
      (B.coq_Term, coq_SHeap) B.coq_Pair coq_SPureSpec) coq_Impl coq_Valid

    val write_register :
      Coq_ty.coq_Ty -> B._UU1d479__UU1d46c__UU1d46e_ -> (B.coq_Term,
      (coq_SHeap, (B.coq_Term, coq_SHeap) B.coq_Pair coq_SPureSpec) coq_Impl)
      coq_Impl coq_Valid
   end

  type 'a coq_SHeapSpec =
    (('a, (coq_SHeap, SymProp.coq_SymProp) coq_Impl) coq_Impl coq_Box,
    (coq_SHeap, SymProp.coq_SymProp) coq_Impl) coq_Impl

  module SHeapSpec :
   sig
    val run :
      (B.coq_Unit coq_SHeapSpec, SymProp.coq_SymProp) coq_Impl coq_Valid

    val lift_purespec :
      ('a1 coq_SPureSpec, 'a1 coq_SHeapSpec) coq_Impl coq_Valid

    val pure : ('a1, 'a1 coq_SHeapSpec) coq_Impl coq_Valid

    val bind :
      ('a1 coq_SHeapSpec, (('a1, 'a2 coq_SHeapSpec) coq_Impl coq_Box, 'a2
      coq_SHeapSpec) coq_Impl) coq_Impl coq_Valid

    module Coq_notations :
     sig
     end

    val error :
      ((coq_SHeap, B.Coq_amsg.coq_AMessage) coq_Impl, 'a1 coq_SHeapSpec)
      coq_Impl coq_Valid

    val angelic :
      lVar option -> (Coq_ty.coq_Ty, B.coq_Term coq_SHeapSpec) coq_Forall
      coq_Valid

    val demonic :
      lVar option -> (Coq_ty.coq_Ty, B.coq_Term coq_SHeapSpec) coq_Forall
      coq_Valid

    val angelic_ctx :
      ('a1 -> lVar) -> (('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx, ('a1, Coq_ty.coq_Ty, B.coq_Term) namedEnv
      coq_SHeapSpec) coq_Forall coq_Valid

    val demonic_ctx :
      ('a1 -> lVar) -> (('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx, ('a1, Coq_ty.coq_Ty, B.coq_Term) namedEnv
      coq_SHeapSpec) coq_Forall coq_Valid

    val angelic_binary :
      ('a1 coq_SHeapSpec, ('a1 coq_SHeapSpec, 'a1 coq_SHeapSpec) coq_Impl)
      coq_Impl coq_Valid

    val demonic_binary :
      ('a1 coq_SHeapSpec, ('a1 coq_SHeapSpec, 'a1 coq_SHeapSpec) coq_Impl)
      coq_Impl coq_Valid

    val debug :
      ((coq_SHeap, B.Coq_amsg.coq_AMessage) coq_Impl, ('a1 coq_SHeapSpec, 'a1
      coq_SHeapSpec) coq_Impl) coq_Impl coq_Valid

    val assert_formula :
      ((coq_SHeap, B.Coq_amsg.coq_AMessage) coq_Impl, (coq_Formula,
      B.coq_Unit coq_SHeapSpec) coq_Impl) coq_Impl coq_Valid

    val assume_formula :
      (coq_Formula, B.coq_Unit coq_SHeapSpec) coq_Impl coq_Valid

    val produce_chunk :
      (coq_Chunk, B.coq_Unit coq_SHeapSpec) coq_Impl coq_Valid

    val consume_chunk :
      (coq_Chunk, B.coq_Unit coq_SHeapSpec) coq_Impl coq_Valid

    val consume_chunk_angelic :
      (coq_Chunk, B.coq_Unit coq_SHeapSpec) coq_Impl coq_Valid

    val read_register :
      Coq_ty.coq_Ty -> B._UU1d479__UU1d46c__UU1d46e_ -> B.coq_Term
      coq_SHeapSpec coq_Valid

    val write_register :
      Coq_ty.coq_Ty -> B._UU1d479__UU1d46c__UU1d46e_ -> (B.coq_Term,
      B.coq_Term coq_SHeapSpec) coq_Impl coq_Valid

    val produce :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_asn.coq_Assertion -> (B.coq_Sub, B.coq_Unit coq_SHeapSpec) coq_Impl
      coq_Valid

    val consume :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_asn.coq_Assertion -> (B.coq_Sub, B.coq_Unit coq_SHeapSpec) coq_Impl
      coq_Valid

    val call_contract :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_SepContract -> (B.coq_SStore, B.coq_Term
      coq_SHeapSpec) coq_Impl coq_Valid

    val call_lemma :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Lemma
      -> (B.coq_SStore, B.coq_Unit coq_SHeapSpec) coq_Impl coq_Valid
   end

  val coq_RPureSpec :
    ('a1, 'a2) Coq_logicalrelation.coq_Rel -> ('a1 coq_SPureSpec, 'a2
    coq_CPureSpec) Coq_logicalrelation.coq_Rel

  module PureSpec :
   sig
    val coq_RPureSpec :
      ('a1, 'a2) Coq_logicalrelation.coq_Rel -> ('a1 coq_SPureSpec, 'a2
      coq_CPureSpec) Coq_logicalrelation.coq_Rel
   end

  val coq_RHeapSpec :
    ('a1, 'a2) Coq_logicalrelation.coq_Rel -> ('a1 coq_SHeapSpec, 'a2
    coq_CHeapSpec) Coq_logicalrelation.coq_Rel

  module HeapSpec :
   sig
   end
 end) ->
 functor (PROG:sig
  type _UU1d46d_

  type _UU1d46d__UU1d47f_

  type _UU1d473_

  type coq_Stm =
  | Coq_stm_val of Coq_ty.coq_Val
  | Coq_stm_exp of B.coq_Exp
  | Coq_stm_let of pVar * Coq_ty.coq_Ty * coq_Stm * coq_Stm
  | Coq_stm_block of (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (pVar, Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv * coq_Stm
  | Coq_stm_assign of pVar
     * (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In * coq_Stm
  | Coq_stm_call of (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * _UU1d46d_ * (pVar, Coq_ty.coq_Ty, B.coq_Exp) namedEnv
  | Coq_stm_call_frame of (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
                          Coq_ctx.coq_Ctx
     * (pVar, Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv * coq_Stm
  | Coq_stm_foreign of (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
                       Coq_ctx.coq_Ctx
     * _UU1d46d__UU1d47f_ * (pVar, Coq_ty.coq_Ty, B.coq_Exp) namedEnv
  | Coq_stm_lemmak of (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
                      Coq_ctx.coq_Ctx
     * _UU1d473_ * (pVar, Coq_ty.coq_Ty, B.coq_Exp) namedEnv * coq_Stm
  | Coq_stm_seq of Coq_ty.coq_Ty * coq_Stm * coq_Stm
  | Coq_stm_assertk of B.coq_Exp * B.coq_Exp * coq_Stm
  | Coq_stm_fail of Coq_ty.coq_Val
  | Coq_stm_pattern_match of Coq_ty.coq_Ty * coq_Stm * pVar B.coq_Pattern
     * (pVar B.coq_PatternCase -> coq_Stm)
  | Coq_stm_read_register of B._UU1d479__UU1d46c__UU1d46e_
  | Coq_stm_write_register of B._UU1d479__UU1d46c__UU1d46e_ * B.coq_Exp
  | Coq_stm_bind of Coq_ty.coq_Ty * coq_Stm * (Coq_ty.coq_Val -> coq_Stm)
  | Coq_stm_debugk of coq_Stm

  val coq_Stm_rect :
    ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Val -> 'a1) -> ((pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> B.coq_Exp -> 'a1)
    -> ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> pVar -> Coq_ty.coq_Ty -> coq_Stm -> 'a1 -> coq_Stm ->
    'a1 -> 'a1) -> ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> Coq_ty.coq_Ty -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (pVar, Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv ->
    coq_Stm -> 'a1 -> 'a1) -> ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> pVar -> (pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_Stm -> 'a1 -> 'a1) -> ((pVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> _UU1d46d_ ->
    (pVar, Coq_ty.coq_Ty, B.coq_Exp) namedEnv -> 'a1) -> ((pVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
    Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv -> coq_Stm -> 'a1 -> 'a1) ->
    ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> _UU1d46d__UU1d47f_ -> (pVar, Coq_ty.coq_Ty, B.coq_Exp)
    namedEnv -> 'a1) -> ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> (pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> _UU1d473_ -> (pVar, Coq_ty.coq_Ty,
    B.coq_Exp) namedEnv -> coq_Stm -> 'a1 -> 'a1) -> ((pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    coq_Stm -> 'a1 -> coq_Stm -> 'a1 -> 'a1) -> ((pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> B.coq_Exp ->
    B.coq_Exp -> coq_Stm -> 'a1 -> 'a1) -> ((pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> Coq_ty.coq_Val ->
    'a1) -> ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_Stm -> 'a1 -> pVar B.coq_Pattern ->
    (pVar B.coq_PatternCase -> coq_Stm) -> (pVar B.coq_PatternCase -> 'a1) ->
    'a1) -> ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> B._UU1d479__UU1d46c__UU1d46e_ -> 'a1) -> ((pVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    B._UU1d479__UU1d46c__UU1d46e_ -> B.coq_Exp -> 'a1) -> ((pVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> coq_Stm -> 'a1 -> (Coq_ty.coq_Val -> coq_Stm) ->
    (Coq_ty.coq_Val -> 'a1) -> 'a1) -> ((pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> coq_Stm -> 'a1 ->
    'a1) -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Stm -> 'a1

  val coq_Stm_rec :
    ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Val -> 'a1) -> ((pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> B.coq_Exp -> 'a1)
    -> ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> pVar -> Coq_ty.coq_Ty -> coq_Stm -> 'a1 -> coq_Stm ->
    'a1 -> 'a1) -> ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> Coq_ty.coq_Ty -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (pVar, Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv ->
    coq_Stm -> 'a1 -> 'a1) -> ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> pVar -> (pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_Stm -> 'a1 -> 'a1) -> ((pVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> _UU1d46d_ ->
    (pVar, Coq_ty.coq_Ty, B.coq_Exp) namedEnv -> 'a1) -> ((pVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
    Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv -> coq_Stm -> 'a1 -> 'a1) ->
    ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> _UU1d46d__UU1d47f_ -> (pVar, Coq_ty.coq_Ty, B.coq_Exp)
    namedEnv -> 'a1) -> ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> (pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> _UU1d473_ -> (pVar, Coq_ty.coq_Ty,
    B.coq_Exp) namedEnv -> coq_Stm -> 'a1 -> 'a1) -> ((pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    coq_Stm -> 'a1 -> coq_Stm -> 'a1 -> 'a1) -> ((pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> B.coq_Exp ->
    B.coq_Exp -> coq_Stm -> 'a1 -> 'a1) -> ((pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> Coq_ty.coq_Val ->
    'a1) -> ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_Stm -> 'a1 -> pVar B.coq_Pattern ->
    (pVar B.coq_PatternCase -> coq_Stm) -> (pVar B.coq_PatternCase -> 'a1) ->
    'a1) -> ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> B._UU1d479__UU1d46c__UU1d46e_ -> 'a1) -> ((pVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    B._UU1d479__UU1d46c__UU1d46e_ -> B.coq_Exp -> 'a1) -> ((pVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> coq_Stm -> 'a1 -> (Coq_ty.coq_Val -> coq_Stm) ->
    (Coq_ty.coq_Val -> 'a1) -> 'a1) -> ((pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> coq_Stm -> 'a1 ->
    'a1) -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Stm -> 'a1

  val coq_NoConfusionHomPackage_Stm :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Stm noConfusionPackage

  type coq_Stm_sig = coq_Stm

  val coq_Stm_sig_pack :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Stm -> ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx * Coq_ty.coq_Ty) * coq_Stm

  val coq_Stm_Signature :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> (coq_Stm, (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx * Coq_ty.coq_Ty, coq_Stm_sig) signature

  val stm_assert :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> B.coq_Exp ->
    B.coq_Exp -> coq_Stm

  val stm_lemma :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> _UU1d473_ -> (pVar,
    Coq_ty.coq_Ty, B.coq_Exp) namedEnv -> coq_Stm

  val stm_if :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Stm -> coq_Stm -> coq_Stm -> coq_Stm

  val stm_match_prod :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_Stm -> pVar ->
    pVar -> coq_Stm -> coq_Stm

  val stm_match_tuple :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Stm -> pVar B.coq_TuplePat ->
    coq_Stm -> coq_Stm

  val stm_match_record :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.recordi -> (pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Stm -> pVar B.coq_RecordPat ->
    coq_Stm -> coq_Stm

  val stm_match_bvec_split :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> nat -> nat -> coq_Stm -> pVar -> pVar -> coq_Stm ->
    coq_Stm

  val stm_match_list :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_Stm -> coq_Stm -> pVar -> pVar ->
    coq_Stm -> coq_Stm

  val stm_match_sum :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_Stm -> pVar ->
    coq_Stm -> pVar -> coq_Stm -> coq_Stm

  val stm_match_enum :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.enumi -> coq_Stm -> (Coq_ty.enumt -> coq_Stm) ->
    coq_Stm

  val stm_match_bvec :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> nat -> coq_Stm -> (Coq_bv.bv -> coq_Stm) -> coq_Stm

  val stm_match_union_alt :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.unioni -> coq_Stm -> (Coq_ty.unionk -> (pVar,
    coq_Stm) B.coq_Alternative) -> coq_Stm

  type coq_UnionAlt = (pVar, coq_Stm) B.coq_Alternative

  type coq_UnionAlts = (Coq_ty.unionk, coq_UnionAlt) sigT list

  val findUnionAlt :
    Coq_ty.unioni -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> Coq_ty.unionk -> coq_UnionAlts ->
    coq_UnionAlt option

  val stm_match_union_alt_list :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.unioni -> coq_Stm -> coq_UnionAlts -> coq_Stm

  val stm_bindfree :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Stm -> bool

  val exp_smart_var :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> pVar ->
    Coq_ty.coq_Ty isSome -> B.coq_Exp

  val stm_smart_assign :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> pVar ->
    Coq_ty.coq_Ty isSome -> coq_Stm -> coq_Stm

  type coq_RegStore

  val read_register :
    coq_RegStore -> Coq_ty.coq_Ty -> B._UU1d479__UU1d46c__UU1d46e_ ->
    Coq_ty.coq_Val

  val write_register :
    coq_RegStore -> Coq_ty.coq_Ty -> B._UU1d479__UU1d46c__UU1d46e_ ->
    Coq_ty.coq_Val -> coq_RegStore

  val coq_FunDef :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> _UU1d46d_ -> coq_Stm

  module Coq_callgraph :
   sig
    type coq_Node = { _UU0394_ : (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
                                 Coq_ctx.coq_Ctx;
                      _UU03c4_ : Coq_ty.coq_Ty; f : _UU1d46d_ }

    val _UU0394_ :
      coq_Node -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

    val _UU03c4_ : coq_Node -> Coq_ty.coq_Ty

    val f : coq_Node -> _UU1d46d_

    type coq_CallGraph = coq_Node -> coq_Node list

    val coq_InvokedByStmList :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_Stm -> coq_Node list
   end

  val generic_call_graph : Coq_callgraph.coq_CallGraph

  module AccessibleTactics :
   sig
   end

  val _UU1d46d__call_graph : Coq_callgraph.coq_CallGraph

  val _UU1d46d__accessible :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> _UU1d46d_ -> __ option
 end) ->
 functor (FL:FailLogic) ->
 functor (SPEC:sig
  type coq_SepContractEnv =
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> PROG._UU1d46d_ -> SIG.coq_SepContract option

  type coq_SepContractEnvEx =
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> PROG._UU1d46d__UU1d47f_ -> SIG.coq_SepContract

  type coq_LemmaEnv =
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    PROG._UU1d473_ -> SIG.coq_Lemma

  val coq_CEnv : coq_SepContractEnv

  val coq_CEnvEx : coq_SepContractEnvEx

  val coq_LEnv : coq_LemmaEnv
 end) ->
 sig
  type coq_DebugCall = { debug_call_function_parameters : (pVar,
                                                          Coq_ty.coq_Ty)
                                                          Binding.coq_Binding
                                                          Coq_ctx.coq_Ctx;
                         debug_call_function_result_type : Coq_ty.coq_Ty;
                         debug_call_function_name : PROG._UU1d46d_;
                         debug_call_function_contract : SIG.coq_SepContract
                                                        option;
                         debug_call_function_arguments : B.coq_SStore;
                         debug_call_pathcondition : SIG.coq_PathCondition;
                         debug_call_heap : SIG.coq_SHeap }

  val debug_call_function_parameters :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCall -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  val debug_call_function_result_type :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCall -> Coq_ty.coq_Ty

  val debug_call_function_name :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCall -> PROG._UU1d46d_

  val debug_call_function_contract :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCall -> SIG.coq_SepContract option

  val debug_call_function_arguments :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCall -> B.coq_SStore

  val debug_call_pathcondition :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCall -> SIG.coq_PathCondition

  val debug_call_heap :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCall -> SIG.coq_SHeap

  type coq_EDebugCall = { edebug_call_function_parameters : (pVar,
                                                            Coq_ty.coq_Ty)
                                                            Binding.coq_Binding
                                                            Coq_ctx.coq_Ctx;
                          edebug_call_function_result_type : Coq_ty.coq_Ty;
                          edebug_call_function_name : PROG._UU1d46d_;
                          edebug_call_function_contract : SIG.coq_SepContract
                                                          option;
                          edebug_call_function_arguments : (pVar,
                                                           Coq_ty.coq_Ty,
                                                           B.coq_ETerm)
                                                           namedEnv;
                          edebug_call_pathcondition : SIG.coq_EFormula list;
                          edebug_call_heap : SIG.coq_EChunk list }

  val edebug_call_function_parameters :
    coq_EDebugCall -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val edebug_call_function_result_type : coq_EDebugCall -> Coq_ty.coq_Ty

  val edebug_call_function_name : coq_EDebugCall -> PROG._UU1d46d_

  val edebug_call_function_contract :
    coq_EDebugCall -> SIG.coq_SepContract option

  val edebug_call_function_arguments :
    coq_EDebugCall -> (pVar, Coq_ty.coq_Ty, B.coq_ETerm) namedEnv

  val edebug_call_pathcondition : coq_EDebugCall -> SIG.coq_EFormula list

  val edebug_call_heap : coq_EDebugCall -> SIG.coq_EChunk list

  val coq_EraseDebugCall : (coq_DebugCall, coq_EDebugCall) B.coq_Erase

  type coq_DebugCallLemma = { debug_call_lemma_parameters : (pVar,
                                                            Coq_ty.coq_Ty)
                                                            Binding.coq_Binding
                                                            Coq_ctx.coq_Ctx;
                              debug_call_lemma_name : PROG._UU1d473_;
                              debug_call_lemma_contract : SIG.coq_Lemma;
                              debug_call_lemma_arguments : B.coq_SStore;
                              debug_call_lemma_pathcondition : SIG.coq_PathCondition;
                              debug_call_lemma_heap : SIG.coq_SHeap }

  val debug_call_lemma_parameters :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCallLemma -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val debug_call_lemma_name :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCallLemma -> PROG._UU1d473_

  val debug_call_lemma_contract :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCallLemma -> SIG.coq_Lemma

  val debug_call_lemma_arguments :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCallLemma -> B.coq_SStore

  val debug_call_lemma_pathcondition :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCallLemma -> SIG.coq_PathCondition

  val debug_call_lemma_heap :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCallLemma -> SIG.coq_SHeap

  type coq_EDebugCallLemma = { edebug_call_lemma_parameters : (pVar,
                                                              Coq_ty.coq_Ty)
                                                              Binding.coq_Binding
                                                              Coq_ctx.coq_Ctx;
                               edebug_call_lemma_name : PROG._UU1d473_;
                               edebug_call_lemma_contract : SIG.coq_Lemma;
                               edebug_call_lemma_arguments : (pVar,
                                                             Coq_ty.coq_Ty,
                                                             B.coq_ETerm)
                                                             namedEnv;
                               edebug_call_lemma_pathcondition : SIG.coq_EFormula
                                                                 list;
                               edebug_call_lemma_heap : SIG.coq_EChunk list }

  val edebug_call_lemma_parameters :
    coq_EDebugCallLemma -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val edebug_call_lemma_name : coq_EDebugCallLemma -> PROG._UU1d473_

  val edebug_call_lemma_contract : coq_EDebugCallLemma -> SIG.coq_Lemma

  val edebug_call_lemma_arguments :
    coq_EDebugCallLemma -> (pVar, Coq_ty.coq_Ty, B.coq_ETerm) namedEnv

  val edebug_call_lemma_pathcondition :
    coq_EDebugCallLemma -> SIG.coq_EFormula list

  val edebug_call_lemma_heap : coq_EDebugCallLemma -> SIG.coq_EChunk list

  val coq_EraseDebugCallLemma :
    (coq_DebugCallLemma, coq_EDebugCallLemma) B.coq_Erase

  val coq_SubstDebugCallLemma : coq_DebugCallLemma B.coq_Subst

  val coq_SubstSUDebugCallLemma :
    'a1 B.coq_SubstUniv -> ('a1, coq_DebugCallLemma) B.coq_SubstSU

  val coq_SubstLawsDebugCallLemma : coq_DebugCallLemma B.coq_SubstLaws

  val coq_OccursCheckDebugCallLemma : coq_DebugCallLemma B.coq_OccursCheck

  val coq_GenOccursCheckDebugCallLemma :
    (B.coq_WeakensTo, coq_DebugCallLemma) B.coq_GenOccursCheck

  val coq_SubstDebugCall : coq_DebugCall B.coq_Subst

  val coq_SubstSUDebugCall :
    'a1 B.coq_SubstUniv -> ('a1, coq_DebugCall) B.coq_SubstSU

  val coq_SubstLawsDebugCall : coq_DebugCall B.coq_SubstLaws

  val coq_OccursCheckDebugCall : coq_DebugCall B.coq_OccursCheck

  val coq_GenOccursCheckDebugCall :
    (B.coq_WeakensTo, coq_DebugCall) B.coq_GenOccursCheck

  type coq_DebugStm = { debug_stm_program_context : (pVar, Coq_ty.coq_Ty)
                                                    Binding.coq_Binding
                                                    Coq_ctx.coq_Ctx;
                        debug_stm_statement_type : Coq_ty.coq_Ty;
                        debug_stm_statement : PROG.coq_Stm;
                        debug_stm_pathcondition : SIG.coq_PathCondition;
                        debug_stm_localstore : B.coq_SStore;
                        debug_stm_heap : SIG.coq_SHeap }

  val debug_stm_program_context :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DebugStm
    -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  val debug_stm_statement_type :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DebugStm
    -> Coq_ty.coq_Ty

  val debug_stm_statement :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DebugStm
    -> PROG.coq_Stm

  val debug_stm_pathcondition :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DebugStm
    -> SIG.coq_PathCondition

  val debug_stm_localstore :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DebugStm
    -> B.coq_SStore

  val debug_stm_heap :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DebugStm
    -> SIG.coq_SHeap

  type coq_EDebugStm = { edebug_stm_program_context : (pVar, Coq_ty.coq_Ty)
                                                      Binding.coq_Binding
                                                      Coq_ctx.coq_Ctx;
                         edebug_stm_statement_type : Coq_ty.coq_Ty;
                         edebug_stm_statement : PROG.coq_Stm;
                         edebug_stm_pathcondition : SIG.coq_EFormula list;
                         edebug_stm_localstore : (pVar, Coq_ty.coq_Ty,
                                                 B.coq_ETerm) namedEnv;
                         edebug_stm_heap : SIG.coq_EChunk list }

  val edebug_stm_program_context :
    coq_EDebugStm -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  val edebug_stm_statement_type : coq_EDebugStm -> Coq_ty.coq_Ty

  val edebug_stm_statement : coq_EDebugStm -> PROG.coq_Stm

  val edebug_stm_pathcondition : coq_EDebugStm -> SIG.coq_EFormula list

  val edebug_stm_localstore :
    coq_EDebugStm -> (pVar, Coq_ty.coq_Ty, B.coq_ETerm) namedEnv

  val edebug_stm_heap : coq_EDebugStm -> SIG.coq_EChunk list

  val coq_EraseDebugStm : (coq_DebugStm, coq_EDebugStm) B.coq_Erase

  val coq_SubstDebugStm : coq_DebugStm B.coq_Subst

  val coq_SubstSUDebugStm :
    'a1 B.coq_SubstUniv -> ('a1, coq_DebugStm) B.coq_SubstSU

  val coq_SubstLawsDebugStm : coq_DebugStm B.coq_SubstLaws

  val coq_OccursCheckDebugStm : coq_DebugStm B.coq_OccursCheck

  val coq_GenOccursCheckDebugStm :
    (B.coq_WeakensTo, coq_DebugStm) B.coq_GenOccursCheck

  type coq_ErrorNoFuel = { error_no_fuel_call_parameter_types : (pVar,
                                                                Coq_ty.coq_Ty)
                                                                Binding.coq_Binding
                                                                Coq_ctx.coq_Ctx;
                           error_no_fuel_call_return_type : Coq_ty.coq_Ty;
                           error_no_fuel_call_function : PROG._UU1d46d_;
                           error_no_fuel_call_arguments : B.coq_SStore;
                           error_no_fuel_pathcondition : SIG.coq_PathCondition;
                           error_no_fuel_heap : SIG.coq_SHeap }

  val error_no_fuel_call_parameter_types :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_ErrorNoFuel -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val error_no_fuel_call_return_type :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_ErrorNoFuel -> Coq_ty.coq_Ty

  val error_no_fuel_call_function :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_ErrorNoFuel -> PROG._UU1d46d_

  val error_no_fuel_call_arguments :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_ErrorNoFuel -> B.coq_SStore

  val error_no_fuel_pathcondition :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_ErrorNoFuel -> SIG.coq_PathCondition

  val error_no_fuel_heap :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_ErrorNoFuel -> SIG.coq_SHeap

  type coq_EErrorNoFuel = { eerror_no_fuel_call_parameter_types : (pVar,
                                                                  Coq_ty.coq_Ty)
                                                                  Binding.coq_Binding
                                                                  Coq_ctx.coq_Ctx;
                            eerror_no_fuel_call_return_type : Coq_ty.coq_Ty;
                            eerror_no_fuel_call_function : PROG._UU1d46d_;
                            eerror_no_fuel_call_arguments : (pVar,
                                                            Coq_ty.coq_Ty,
                                                            B.coq_ETerm)
                                                            namedEnv;
                            eerror_no_fuel_pathcondition : SIG.coq_EFormula
                                                           list;
                            eerror_no_fuel_heap : SIG.coq_EChunk list }

  val eerror_no_fuel_call_parameter_types :
    coq_EErrorNoFuel -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val eerror_no_fuel_call_return_type : coq_EErrorNoFuel -> Coq_ty.coq_Ty

  val eerror_no_fuel_call_function : coq_EErrorNoFuel -> PROG._UU1d46d_

  val eerror_no_fuel_call_arguments :
    coq_EErrorNoFuel -> (pVar, Coq_ty.coq_Ty, B.coq_ETerm) namedEnv

  val eerror_no_fuel_pathcondition : coq_EErrorNoFuel -> SIG.coq_EFormula list

  val eerror_no_fuel_heap : coq_EErrorNoFuel -> SIG.coq_EChunk list

  val coq_EraseErrorNoFuel : (coq_ErrorNoFuel, coq_EErrorNoFuel) B.coq_Erase

  val coq_SubstErrorNoFuel : coq_ErrorNoFuel B.coq_Subst

  val coq_SubstSUErrorNoFuel :
    'a1 B.coq_SubstUniv -> ('a1, coq_ErrorNoFuel) B.coq_SubstSU

  val coq_SubstLawsErrorNoFuel : coq_ErrorNoFuel B.coq_SubstLaws

  val coq_OccursCheckErrorNoFuel : coq_ErrorNoFuel B.coq_OccursCheck

  val coq_GenOccursCheckErrorNoFuel :
    (B.coq_WeakensTo, coq_ErrorNoFuel) B.coq_GenOccursCheck

  val coq_VerificationCondition_rect :
    SIG.SymProp.coq_SymProp -> (__ -> 'a1) -> 'a1

  val coq_VerificationCondition_rec :
    SIG.SymProp.coq_SymProp -> (__ -> 'a1) -> 'a1

  val coq_VerificationConditionWithErasure_rect :
    SIG.Erasure.coq_ESymProp -> (__ -> 'a1) -> 'a1

  val coq_VerificationConditionWithErasure_rec :
    SIG.Erasure.coq_ESymProp -> (__ -> 'a1) -> 'a1

  type coq_Config = { config_debug_function : ((pVar, Coq_ty.coq_Ty)
                                              Binding.coq_Binding
                                              Coq_ctx.coq_Ctx ->
                                              Coq_ty.coq_Ty -> PROG._UU1d46d_
                                              -> bool);
                      config_debug_lemma : ((pVar, Coq_ty.coq_Ty)
                                           Binding.coq_Binding
                                           Coq_ctx.coq_Ctx -> PROG._UU1d473_
                                           -> bool) }

  val config_debug_function :
    coq_Config -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> Coq_ty.coq_Ty -> PROG._UU1d46d_ -> bool

  val config_debug_lemma :
    coq_Config -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> PROG._UU1d473_ -> bool

  val default_config : coq_Config

  type 'a coq_SStoreSpec =
    (('a, (B.coq_SStore, (SIG.coq_SHeap, SIG.SymProp.coq_SymProp)
    SIG.coq_Impl) SIG.coq_Impl) SIG.coq_Impl SIG.coq_Box, (B.coq_SStore,
    (SIG.coq_SHeap, SIG.SymProp.coq_SymProp) SIG.coq_Impl) SIG.coq_Impl)
    SIG.coq_Impl

  type coq_ExecCall =
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> PROG._UU1d46d_ -> (B.coq_SStore, B.coq_Term
    SIG.coq_SHeapSpec) SIG.coq_Impl SIG.coq_Valid

  type coq_ExecCallForeign =
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> PROG._UU1d46d__UU1d47f_ -> (B.coq_SStore, B.coq_Term
    SIG.coq_SHeapSpec) SIG.coq_Impl SIG.coq_Valid

  type coq_ExecLemma =
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    PROG._UU1d473_ -> (B.coq_SStore, B.coq_Unit SIG.coq_SHeapSpec)
    SIG.coq_Impl SIG.coq_Valid

  type coq_ExecFail =
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Val -> B.coq_Term coq_SStoreSpec SIG.coq_Valid

  type coq_Exec =
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> PROG.coq_Stm -> B.coq_Term coq_SStoreSpec SIG.coq_Valid

  module SStoreSpec :
   sig
    val evalStoreSpec :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
      coq_SStoreSpec, (B.coq_SStore, 'a1 SIG.coq_SHeapSpec) SIG.coq_Impl)
      SIG.coq_Impl SIG.coq_Valid

    val lift_purespec :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
      SIG.coq_SPureSpec, 'a1 coq_SStoreSpec) SIG.coq_Impl SIG.coq_Valid

    val lift_heapspec :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
      SIG.coq_SHeapSpec, 'a1 coq_SStoreSpec) SIG.coq_Impl SIG.coq_Valid

    val pure :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, 'a1
      coq_SStoreSpec) SIG.coq_Impl SIG.coq_Valid

    val bind :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
      coq_SStoreSpec, (('a1, 'a2 coq_SStoreSpec) SIG.coq_Impl SIG.coq_Box,
      'a2 coq_SStoreSpec) SIG.coq_Impl) SIG.coq_Impl SIG.coq_Valid

    val error :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ((B.coq_SStore,
      (SIG.coq_SHeap, B.Coq_amsg.coq_AMessage) SIG.coq_Impl) SIG.coq_Impl,
      'a1 coq_SStoreSpec) SIG.coq_Impl SIG.coq_Valid

    val block :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1
      coq_SStoreSpec SIG.coq_Valid

    val angelic_binary :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
      coq_SStoreSpec, ('a1 coq_SStoreSpec, 'a1 coq_SStoreSpec) SIG.coq_Impl)
      SIG.coq_Impl SIG.coq_Valid

    val demonic_binary :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
      coq_SStoreSpec, ('a1 coq_SStoreSpec, 'a1 coq_SStoreSpec) SIG.coq_Impl)
      SIG.coq_Impl SIG.coq_Valid

    val angelic :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar
      option -> (Coq_ty.coq_Ty, B.coq_Term coq_SStoreSpec) SIG.coq_Forall
      SIG.coq_Valid

    val demonic :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar
      option -> (Coq_ty.coq_Ty, B.coq_Term coq_SStoreSpec) SIG.coq_Forall
      SIG.coq_Valid

    val debug :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ((B.coq_SStore,
      (SIG.coq_SHeap, B.Coq_amsg.coq_AMessage) SIG.coq_Impl) SIG.coq_Impl,
      ('a1 coq_SStoreSpec, 'a1 coq_SStoreSpec) SIG.coq_Impl) SIG.coq_Impl
      SIG.coq_Valid

    val angelic_ctx :
      ('a1 -> lVar) -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx, ('a1, Coq_ty.coq_Ty, B.coq_Term) namedEnv
      coq_SStoreSpec) SIG.coq_Forall SIG.coq_Valid

    val demonic_ctx :
      ('a1 -> lVar) -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx, ('a1, Coq_ty.coq_Ty, B.coq_Term) namedEnv
      coq_SStoreSpec) SIG.coq_Forall SIG.coq_Valid

    module Coq_notations :
     sig
     end

    val demonic_pattern_match :
      ('a1 -> lVar) -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 B.coq_Pattern -> (B.coq_Term,
      'a1 B.coq_SMatchResult coq_SStoreSpec) SIG.coq_Impl SIG.coq_Valid

    val pushpop :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> pVar ->
      Coq_ty.coq_Ty -> (B.coq_Term, ('a1 coq_SStoreSpec, 'a1 coq_SStoreSpec)
      SIG.coq_Impl) SIG.coq_Impl SIG.coq_Valid

    val pushspops :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (B.coq_SStore,
      ('a1 coq_SStoreSpec, 'a1 coq_SStoreSpec) SIG.coq_Impl) SIG.coq_Impl
      SIG.coq_Valid

    val get_local :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      B.coq_SStore coq_SStoreSpec SIG.coq_Valid

    val put_local :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (B.coq_SStore,
      B.coq_Unit coq_SStoreSpec) SIG.coq_Impl SIG.coq_Valid

    val eval_exp :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> B.coq_Exp -> B.coq_Term coq_SStoreSpec SIG.coq_Valid

    val eval_exps :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty, B.coq_Exp) namedEnv -> B.coq_SStore coq_SStoreSpec
      SIG.coq_Valid

    val assign :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> pVar ->
      Coq_ty.coq_Ty -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> (B.coq_Term, B.coq_Unit coq_SStoreSpec) SIG.coq_Impl
      SIG.coq_Valid

    val exec_aux :
      coq_ExecCallForeign -> coq_ExecLemma -> coq_ExecCall -> coq_ExecFail ->
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> PROG.coq_Stm -> B.coq_Term coq_SStoreSpec SIG.coq_Valid
   end

  val exec_contract :
    coq_Exec -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> SIG.coq_SepContract -> PROG.coq_Stm -> B.coq_Unit
    SIG.coq_SHeapSpec SIG.coq_Valid

  val exec_call_error_no_fuel : coq_ExecCall

  val sexec_call_foreign : coq_ExecCallForeign

  val debug_lemma :
    coq_Config -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> PROG._UU1d473_ -> (B.coq_SStore, B.coq_Unit SIG.coq_SHeapSpec)
    SIG.coq_Impl SIG.coq_Valid

  val sexec_lemma : coq_Config -> coq_ExecLemma

  val debug_call :
    coq_Config -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> Coq_ty.coq_Ty -> PROG._UU1d46d_ -> (B.coq_SStore, B.coq_Unit
    SIG.coq_SHeapSpec) SIG.coq_Impl SIG.coq_Valid

  val sexec_fail : coq_ExecFail

  val sexec_call : coq_Config -> nat -> coq_ExecCall

  val sexec : coq_Config -> nat -> coq_Exec

  val vcgen :
    coq_Config -> nat -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> SIG.coq_SepContract -> PROG.coq_Stm
    -> SIG.SymProp.coq_SymProp SIG.coq_Valid

  module Symbolic :
   sig
    val verification_failed_with_error : B.Coq_amsg.coq_EAMessage -> bool

    val ok' :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SIG.SymProp.coq_SymProp -> bool

    val ok :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SIG.SymProp.coq_SymProp -> bool

    val coq_VcGenErasureFuel :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> nat -> SIG.coq_SepContract -> PROG.coq_Stm ->
      SIG.Erasure.coq_ESymProp

    val coq_VcGenErasure :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> SIG.coq_SepContract -> PROG.coq_Stm ->
      SIG.Erasure.coq_ESymProp

    module Statistics :
     sig
      val extend_postcond_with_debug :
        (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> SIG.coq_SepContract -> SIG.coq_SepContract

      val calc :
        (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> PROG._UU1d46d_ -> stats option
     end
   end
 end

val xlen : nat

val byte : nat

val bytes_per_word : nat

val bytes_per_instr : nat

val word : nat

val xlenbytes : nat

val xlenbits : nat

val bv_instrsize : nat -> Coq_bv.bv

type xlenbits0 = Coq_bv.bv

type addr = Coq_bv.bv

type word0 = Coq_bv.bv

type byte0 = Coq_bv.bv

val minAddr : n

val lenAddr : n

val maxAddr : n

val mmioStartAddr : n

val mmioLenAddr : n

val mmioAddrs : addr list

val withinMMIODec : addr -> nat -> decision

type minterrupts = { mEI : bool; uEI : bool; mTI : bool; uTI : bool;
                     mSI : bool; uSI : bool }

type mMIOEnv = { state_tra_read : (__ -> addr -> nat -> (__, Coq_bv.bv) prod);
                 state_tra_write : (__ -> addr -> nat -> Coq_bv.bv -> __);
                 state_tra_world_updates : (__ -> (minterrupts, __) prod);
                 state_init : __ }

type state = __

val mmioenv : mMIOEnv

type privilege =
| User
| Machine

type interruptType =
| I_U_Software
| I_M_Software
| I_U_Timer
| I_M_Timer
| I_U_External
| I_M_External

type cSRIdx =
| MStatus
| Mie
| MTvec
| MScratch
| MEpc
| MCause
| MPMP0CFG
| Mip
| MPMPADDR0
| MPMPADDR1

type pmpCfgIdx =
| PMP0CFG
| PMP1CFG

type pmpCfgPerm =
| PmpO
| PmpR
| PmpW
| PmpX
| PmpRW
| PmpRX
| PmpWX
| PmpRWX

type pmpAddrIdx =
| PMPADDR0
| PMPADDR1

type pmpAddrMatchType =
| OFF
| TOR

type pmpMatch =
| PMP_Success
| PMP_Continue
| PMP_Fail

type pmpAddrMatch =
| PMP_NoMatch
| PMP_PartialMatch
| PMP_Match

type rOP =
| RISCV_ADD
| RISCV_SLT
| RISCV_SLTU
| RISCV_AND
| RISCV_OR
| RISCV_XOR
| RISCV_SLL
| RISCV_SRL
| RISCV_SUB
| RISCV_SRA

type iOP =
| RISCV_ADDI
| RISCV_SLTI
| RISCV_SLTIU
| RISCV_ANDI
| RISCV_ORI
| RISCV_XORI

type sOP =
| RISCV_SLLI
| RISCV_SRLI
| RISCV_SRAI

type uOP =
| RISCV_LUI
| RISCV_AUIPC

type bOP =
| RISCV_BEQ
| RISCV_BNE
| RISCV_BLT
| RISCV_BGE
| RISCV_BLTU
| RISCV_BGEU

type cSROP =
| CSRRW
| CSRRS
| CSRRC

type mOP =
| RISCV_MUL
| RISCV_MULH
| RISCV_MULHSU
| RISCV_MULHU

type retired =
| RETIRE_SUCCESS
| RETIRE_FAIL

type wordWidth =
| BYTE
| HALF
| WORD

type enums =
| Privilege
| InterruptType
| Csridx
| Pmpcfgidx
| Pmpcfgperm
| Pmpaddridx
| Pmpaddrmatchtype
| Pmpmatch
| Pmpaddrmatch
| Rop
| Iop
| Sop
| Uop
| Bop
| Csrop
| Retired
| Wordwidth
| Mop

type regIdx = Coq_bv.bv

type aST =
| RTYPE of regIdx * regIdx * regIdx * rOP
| ITYPE of Coq_bv.bv * regIdx * regIdx * iOP
| SHIFTIOP of Coq_bv.bv * regIdx * regIdx * sOP
| UTYPE of Coq_bv.bv * regIdx * uOP
| BTYPE of Coq_bv.bv * regIdx * regIdx * bOP
| RISCV_JAL of Coq_bv.bv * regIdx
| RISCV_JALR of Coq_bv.bv * regIdx * regIdx
| LOAD of Coq_bv.bv * regIdx * regIdx * bool * wordWidth
| STORE of Coq_bv.bv * regIdx * regIdx * wordWidth
| ECALL
| EBREAK
| MRET
| CSR of cSRIdx * regIdx * regIdx * bool * cSROP
| MUL of regIdx * regIdx * regIdx * bool * bool * bool

type accessType =
| Read
| Write
| ReadWrite
| Execute

type exceptionType =
| E_Fetch_Access_Fault
| E_Load_Access_Fault
| E_SAMO_Access_Fault
| E_U_EnvCall
| E_M_EnvCall
| E_Illegal_Instr

type fetchResult =
| F_Base of word0
| F_Error of exceptionType * xlenbits0

type ctlResult =
| CTL_TRAP of exceptionType
| CTL_MRET

type interruptSet =
| Ints_Pending of minterrupts
| Ints_Delegated of minterrupts
| Ints_Empty

type memoryOpResult =
| MemValue of Coq_bv.bv
| MemException of exceptionType

type aSTConstructor =
| KRTYPE
| KITYPE
| KSHIFTIOP
| KUTYPE
| KBTYPE
| KRISCV_JAL
| KRISCV_JALR
| KLOAD
| KSTORE
| KECALL
| KEBREAK
| KMRET
| KCSR
| KMUL

type accessTypeConstructor =
| KRead
| KWrite
| KReadWrite
| KExecute

type exceptionTypeConstructor =
| KE_Fetch_Access_Fault
| KE_Load_Access_Fault
| KE_SAMO_Access_Fault
| KE_U_EnvCall
| KE_M_EnvCall
| KE_Illegal_Instr

type memoryOpResultConstructor =
| KMemValue
| KMemException

type fetchResultConstructor =
| KF_Base
| KF_Error

type ctlResultConstructor =
| KCTL_TRAP
| KCTL_MRET

type interruptSetConstructor =
| KInts_Pending
| KInts_Delegated
| KInts_Empty

type unions =
| Ast
| Access_type
| Exception_type
| Memory_op_result of nat
| Fetch_result
| Ctl_result
| Interrupt_set

type pmpcfg_ent = { l : bool; a : pmpAddrMatchType; x : bool; w : bool;
                    r : bool }

type mstatus = { mPP : privilege; mPIE : bool; mIE : bool }

type records =
| Rpmpcfg_ent
| Rmstatus
| Rminterrupts

val enums_eqdec : enums -> enums -> enums dec_eq

val enums_EqDec : enums eqDec

val privilege_eqdec : privilege -> privilege -> privilege dec_eq

val privilege_EqDec : privilege eqDec

val cSRIdx_eqdec : cSRIdx -> cSRIdx -> cSRIdx dec_eq

val cSRIdx_EqDec : cSRIdx eqDec

val pmpCfgIdx_eqdec : pmpCfgIdx -> pmpCfgIdx -> pmpCfgIdx dec_eq

val pmpCfgIdx_EqDec : pmpCfgIdx eqDec

val pmpCfgPerm_eqdec : pmpCfgPerm -> pmpCfgPerm -> pmpCfgPerm dec_eq

val pmpCfgPerm_EqDec : pmpCfgPerm eqDec

val pmpAddrIdx_eqdec : pmpAddrIdx -> pmpAddrIdx -> pmpAddrIdx dec_eq

val pmpAddrIdx_EqDec : pmpAddrIdx eqDec

val pmpAddrMatchType_eqdec :
  pmpAddrMatchType -> pmpAddrMatchType -> pmpAddrMatchType dec_eq

val pmpAddrMatchType_EqDec : pmpAddrMatchType eqDec

val pmpMatch_eqdec : pmpMatch -> pmpMatch -> pmpMatch dec_eq

val pmpMatch_EqDec : pmpMatch eqDec

val pmpAddrMatch_eqdec : pmpAddrMatch -> pmpAddrMatch -> pmpAddrMatch dec_eq

val pmpAddrMatch_EqDec : pmpAddrMatch eqDec

val rOP_eqdec : rOP -> rOP -> rOP dec_eq

val rOP_EqDec : rOP eqDec

val iOP_eqdec : iOP -> iOP -> iOP dec_eq

val iOP_EqDec : iOP eqDec

val sOP_eqdec : sOP -> sOP -> sOP dec_eq

val sOP_EqDec : sOP eqDec

val uOP_eqdec : uOP -> uOP -> uOP dec_eq

val uOP_EqDec : uOP eqDec

val bOP_eqdec : bOP -> bOP -> bOP dec_eq

val bOP_EqDec : bOP eqDec

val cSROP_eqdec : cSROP -> cSROP -> cSROP dec_eq

val cSROP_EqDec : cSROP eqDec

val mOP_eqdec : mOP -> mOP -> mOP dec_eq

val mOP_EqDec : mOP eqDec

val retired_eqdec : retired -> retired -> retired dec_eq

val retired_EqDec : retired eqDec

val wordWidth_eqdec : wordWidth -> wordWidth -> wordWidth dec_eq

val wordWidth_EqDec : wordWidth eqDec

val unions_eqdec : unions -> unions -> unions dec_eq

val unions_EqDec : unions eqDec

val aST_eqdec : aST -> aST -> aST dec_eq

val aST_EqDec : aST eqDec

val aSTConstructor_eqdec :
  aSTConstructor -> aSTConstructor -> aSTConstructor dec_eq

val aSTConstructor_EqDec : aSTConstructor eqDec

val accessType_eqdec : accessType -> accessType -> accessType dec_eq

val accessType_EqDec : accessType eqDec

val accessTypeConstructor_eqdec :
  accessTypeConstructor -> accessTypeConstructor -> accessTypeConstructor
  dec_eq

val accessTypeConstructor_EqDec : accessTypeConstructor eqDec

val exceptionType_eqdec :
  exceptionType -> exceptionType -> exceptionType dec_eq

val exceptionType_EqDec : exceptionType eqDec

val exceptionTypeConstructor_eqdec :
  exceptionTypeConstructor -> exceptionTypeConstructor ->
  exceptionTypeConstructor dec_eq

val exceptionTypeConstructor_EqDec : exceptionTypeConstructor eqDec

val fetchResult_eqdec : fetchResult -> fetchResult -> fetchResult dec_eq

val fetchResult_EqDec : fetchResult eqDec

val fetchResultConstructor_eqdec :
  fetchResultConstructor -> fetchResultConstructor -> fetchResultConstructor
  dec_eq

val fetchResultConstructor_EqDec : fetchResultConstructor eqDec

val interruptType_eqdec :
  interruptType -> interruptType -> interruptType dec_eq

val interruptType_EqDec : interruptType eqDec

val ctlResult_eqdec : ctlResult -> ctlResult -> ctlResult dec_eq

val ctlResult_EqDec : ctlResult eqDec

val ctlResultConstructor_eqdec :
  ctlResultConstructor -> ctlResultConstructor -> ctlResultConstructor dec_eq

val ctlResultConstructor_EqDec : ctlResultConstructor eqDec

val interruptSetConstructor_eqdec :
  interruptSetConstructor -> interruptSetConstructor ->
  interruptSetConstructor dec_eq

val interruptSetConstructor_EqDec : interruptSetConstructor eqDec

val memoryOpResult_eqdec :
  nat -> memoryOpResult -> memoryOpResult -> memoryOpResult dec_eq

val memoryOpResult_EqDec : nat -> memoryOpResult eqDec

val memoryOpResultConstructor_eqdec :
  memoryOpResultConstructor -> memoryOpResultConstructor ->
  memoryOpResultConstructor dec_eq

val memoryOpResultConstructor_EqDec : memoryOpResultConstructor eqDec

val records_eqdec : records -> records -> records dec_eq

val records_EqDec : records eqDec

val pmpcfg_ent_eqdec : pmpcfg_ent -> pmpcfg_ent -> pmpcfg_ent dec_eq

val pmpcfg_ent_EqDec : pmpcfg_ent eqDec

val mstatus_eqdec : mstatus -> mstatus -> mstatus dec_eq

val mstatus_EqDec : mstatus eqDec

val minterrupts_eqdec : minterrupts -> minterrupts -> minterrupts dec_eq

val minterrupts_EqDec : minterrupts eqDec

val interruptSet_eqdec : interruptSet -> interruptSet -> interruptSet dec_eq

val interruptSet_EqDec : interruptSet eqDec

val privilege_finite : privilege finite

val cSRIdx_finite : cSRIdx finite

val interruptType_finite : interruptType finite

val pmpCfgIdx_finite : pmpCfgIdx finite

val pmpCfgPerm_finite : pmpCfgPerm finite

val pmpAddrIdx_finite : pmpAddrIdx finite

val pmpAddrMatchType_finite : pmpAddrMatchType finite

val pmpMatch_finite : pmpMatch finite

val pmpAddrMatch_finite : pmpAddrMatch finite

val rOP_finite : rOP finite

val iOP_finite : iOP finite

val sOP_finite : sOP finite

val uOP_finite : uOP finite

val bOP_finite : bOP finite

val cSROP_finite : cSROP finite

val mOP_finite : mOP finite

val retired_finite : retired finite

val wordWidth_finite : wordWidth finite

val aSTConstructor_finite : aSTConstructor finite

val accessTypeConstructor_finite : accessTypeConstructor finite

val exceptionTypeConstructor_finite : exceptionTypeConstructor finite

val fetchResultConstructor_finite : fetchResultConstructor finite

val ctlResultConstructor_finite : ctlResultConstructor finite

val interruptSetConstructor_finite : interruptSetConstructor finite

val memoryOpResultConstructor_finite : memoryOpResultConstructor finite

module RiscvPmpBase :
 sig
  val typedeclkit : Coq_ty.coq_TypeDeclKit

  val ty_xlenbits : Coq_ty.coq_Ty

  val ty_word : Coq_ty.coq_Ty

  val ty_byte : Coq_ty.coq_Ty

  val ty_bytes : nat -> Coq_ty.coq_Ty

  val ty_regno : Coq_ty.coq_Ty

  val ty_privilege : Coq_ty.coq_Ty

  val ty_interruptType : Coq_ty.coq_Ty

  val ty_priv_level : Coq_ty.coq_Ty

  val ty_csridx : Coq_ty.coq_Ty

  val ty_pmpcfgidx : Coq_ty.coq_Ty

  val ty_pmpcfgperm : Coq_ty.coq_Ty

  val ty_pmpaddridx : Coq_ty.coq_Ty

  val ty_pmpaddrmatchtype : Coq_ty.coq_Ty

  val ty_pmpmatch : Coq_ty.coq_Ty

  val ty_pmpaddrmatch : Coq_ty.coq_Ty

  val ty_pmp_addr_range : Coq_ty.coq_Ty

  val ty_rop : Coq_ty.coq_Ty

  val ty_iop : Coq_ty.coq_Ty

  val ty_sop : Coq_ty.coq_Ty

  val ty_uop : Coq_ty.coq_Ty

  val ty_bop : Coq_ty.coq_Ty

  val ty_csrop : Coq_ty.coq_Ty

  val ty_mop : Coq_ty.coq_Ty

  val ty_retired : Coq_ty.coq_Ty

  val ty_word_width : Coq_ty.coq_Ty

  val ty_mcause : Coq_ty.coq_Ty

  val ty_exc_code : Coq_ty.coq_Ty

  val ty_ast : Coq_ty.coq_Ty

  val ty_access_type : Coq_ty.coq_Ty

  val ty_exception_type : Coq_ty.coq_Ty

  val ty_memory_op_result : nat -> Coq_ty.coq_Ty

  val ty_fetch_result : Coq_ty.coq_Ty

  val ty_ctl_result : Coq_ty.coq_Ty

  val ty_interrupt_set : Coq_ty.coq_Ty

  val ty_pmpcfg_ent : Coq_ty.coq_Ty

  val ty_mstatus : Coq_ty.coq_Ty

  val ty_Minterrupts : Coq_ty.coq_Ty

  val ty_pmpentry : Coq_ty.coq_Ty

  val ty_pmpentries : Coq_ty.coq_Ty

  type enum_denote = __

  type union_denote = __

  type record_denote = __

  val typedenotekit : Coq_ty.coq_TypeDenoteKit

  type union_constructor = __

  val union_constructor_type : unions -> union_constructor -> Coq_ty.coq_Ty

  val eqdec_enum_denote : enums -> enum_denote eqDec

  val finite_enum_denote : enums -> enum_denote finite

  val eqdec_union_denote : unions -> union_denote eqDec

  val eqdec_union_constructor : unions -> union_constructor eqDec

  val finite_union_constructor : unions -> union_constructor finite

  val eqdec_record_denote : records -> record_denote eqDec

  val union_unfold :
    Coq_ty.unioni -> Coq_ty.uniont -> (union_constructor, Coq_ty.coq_Val) sigT

  val union_fold :
    Coq_ty.unioni -> (union_constructor, Coq_ty.coq_Val) sigT -> Coq_ty.uniont

  val record_field_type :
    Coq_ty.recordi -> (string, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val record_fold :
    Coq_ty.recordi -> (string, Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv ->
    Coq_ty.recordt

  val record_unfold :
    Coq_ty.recordi -> Coq_ty.recordt -> (string, Coq_ty.coq_Ty,
    Coq_ty.coq_Val) namedEnv

  val typedefkit : Coq_ty.coq_TypeDefKit

  val varkit : varKit

  type coq_Reg =
  | Coq_pc
  | Coq_nextpc
  | Coq_mstatus
  | Coq_mie
  | Coq_mip
  | Coq_mtvec
  | Coq_mcause
  | Coq_mepc
  | Coq_mscratch
  | Coq_cur_privilege
  | Coq_x1
  | Coq_x2
  | Coq_x3
  | Coq_x4
  | Coq_x5
  | Coq_x6
  | Coq_x7
  | Coq_x8
  | Coq_x9
  | Coq_x10
  | Coq_x11
  | Coq_x12
  | Coq_x13
  | Coq_x14
  | Coq_x15
  | Coq_x16
  | Coq_x17
  | Coq_x18
  | Coq_x19
  | Coq_x20
  | Coq_x21
  | Coq_x22
  | Coq_x23
  | Coq_x24
  | Coq_x25
  | Coq_x26
  | Coq_x27
  | Coq_x28
  | Coq_x29
  | Coq_x30
  | Coq_x31
  | Coq_pmp0cfg
  | Coq_pmp1cfg
  | Coq_pmpaddr0
  | Coq_pmpaddr1

  val coq_Reg_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> Coq_ty.coq_Ty -> coq_Reg -> 'a1

  val coq_Reg_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> Coq_ty.coq_Ty -> coq_Reg -> 'a1

  val reg_convert : regIdx -> coq_Reg option

  type coq_Reg_sig = coq_Reg

  val coq_Reg_sig_pack : Coq_ty.coq_Ty -> coq_Reg -> Coq_ty.coq_Ty * coq_Reg

  val coq_Reg_Signature :
    Coq_ty.coq_Ty -> (coq_Reg, Coq_ty.coq_Ty, coq_Reg_sig) signature

  val coq_NoConfusionPackage_Reg :
    (Coq_ty.coq_Ty * coq_Reg) noConfusionPackage

  type _UU1d479__UU1d46c__UU1d46e_ = coq_Reg

  val _UU1d479__UU1d46c__UU1d46e__eq_dec : (Coq_ty.coq_Ty, coq_Reg) sigT eqDec

  val _UU1d479__UU1d46c__UU1d46e__finite :
    (Coq_ty.coq_Ty, coq_Reg) sigT finite

  val val_inhabited : Coq_ty.coq_Ty -> Coq_ty.coq_Val inhabited

  type coq_RAM = addr -> byte0

  type coq_EventTy =
  | IOWrite
  | IORead

  val coq_EventTy_rect : 'a1 -> 'a1 -> coq_EventTy -> 'a1

  val coq_EventTy_rec : 'a1 -> 'a1 -> coq_EventTy -> 'a1

  type coq_Event = { event_type : coq_EventTy; event_addr : addr;
                     event_nbbytes : nat; event_contents : Coq_bv.bv }

  val event_type : coq_Event -> coq_EventTy

  val event_addr : coq_Event -> addr

  val event_nbbytes : coq_Event -> nat

  val event_contents : coq_Event -> Coq_bv.bv

  type coq_Trace = coq_Event list

  type coq_MemoryType = { memory_ram : coq_RAM; memory_trace : coq_Trace;
                          memory_state : state }

  val memory_ram : coq_MemoryType -> coq_RAM

  val memory_trace : coq_MemoryType -> coq_Trace

  val memory_state : coq_MemoryType -> state

  type coq_Memory = coq_MemoryType

  val memory_update_ram : coq_Memory -> coq_RAM -> coq_MemoryType

  val memory_update_trace : coq_Memory -> coq_Trace -> coq_MemoryType

  val memory_append_trace : coq_Memory -> coq_Event -> coq_MemoryType

  val memory_update_state : coq_Memory -> state -> coq_MemoryType

  val fun_read_ram : coq_Memory -> nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val

  val write_byte : coq_RAM -> Coq_ty.coq_Val -> byte0 -> coq_RAM

  val fun_write_ram :
    coq_Memory -> nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val -> coq_Memory

  val fun_within_mmio : nat -> Coq_ty.coq_Val -> bool

  val fun_read_mmio :
    coq_Memory -> nat -> Coq_ty.coq_Val -> (coq_Memory, Coq_ty.coq_Val) prod

  val fun_externalWorldUpdates : coq_Memory -> (minterrupts, coq_Memory) prod

  val fun_write_mmio :
    coq_Memory -> nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val -> coq_Memory

  type coq_Exp =
  | Coq_exp_var of pVar * Coq_ty.coq_Ty
     * (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_exp_val of Coq_ty.coq_Ty * Coq_ty.coq_Val
  | Coq_exp_binop of Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Exp * coq_Exp
  | Coq_exp_unop of Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Exp
  | Coq_exp_list of Coq_ty.coq_Ty * coq_Exp list
  | Coq_exp_bvec of nat * coq_Exp t
  | Coq_exp_tuple of Coq_ty.coq_Ty Coq_ctx.coq_Ctx
     * (Coq_ty.coq_Ty, coq_Exp) Coq_env.coq_Env
  | Coq_exp_union of Coq_ty.unioni * Coq_ty.unionk * coq_Exp
  | Coq_exp_record of Coq_ty.recordi
     * (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Exp) namedEnv

  val coq_Exp_rect :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar ->
    Coq_ty.coq_Ty -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Val -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Exp -> 'a1 ->
    coq_Exp -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Exp -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty -> coq_Exp
    list -> __ -> 'a1) -> (nat -> coq_Exp t -> __ -> 'a1) -> (Coq_ty.coq_Ty
    Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, coq_Exp) Coq_env.coq_Env -> __ -> 'a1)
    -> (Coq_ty.unioni -> Coq_ty.unionk -> coq_Exp -> 'a1 -> 'a1) ->
    (Coq_ty.recordi -> (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Exp) namedEnv ->
    __ -> 'a1) -> Coq_ty.coq_Ty -> coq_Exp -> 'a1

  val coq_Exp_rec :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar ->
    Coq_ty.coq_Ty -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Val -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Exp -> 'a1 ->
    coq_Exp -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Exp -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty -> coq_Exp
    list -> __ -> 'a1) -> (nat -> coq_Exp t -> __ -> 'a1) -> (Coq_ty.coq_Ty
    Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, coq_Exp) Coq_env.coq_Env -> __ -> 'a1)
    -> (Coq_ty.unioni -> Coq_ty.unionk -> coq_Exp -> 'a1 -> 'a1) ->
    (Coq_ty.recordi -> (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Exp) namedEnv ->
    __ -> 'a1) -> Coq_ty.coq_Ty -> coq_Exp -> 'a1

  val eval :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Exp -> (pVar, Coq_ty.coq_Ty, Coq_ty.coq_Val)
    namedEnv -> Coq_ty.coq_Val

  val evals :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
    Coq_ty.coq_Ty, coq_Exp) namedEnv -> (pVar, Coq_ty.coq_Ty, Coq_ty.coq_Val)
    namedEnv -> (pVar, Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv

  val exp_truncate :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> coq_Exp -> coq_Exp

  val exp_vector_subrange :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> nat -> coq_Exp -> coq_Exp

  val exp_update_vector_subrange :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> nat -> coq_Exp -> coq_Exp -> coq_Exp

  type coq_Term =
  | Coq_term_var of lVar * Coq_ty.coq_Ty
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_term_val of Coq_ty.coq_Ty * Coq_ty.coq_Val
  | Coq_term_binop of Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_term_unop of Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term
  | Coq_term_tuple of Coq_ty.coq_Ty Coq_ctx.coq_Ctx
     * (Coq_ty.coq_Ty, coq_Term) Coq_env.coq_Env
  | Coq_term_union of Coq_ty.unioni * Coq_ty.unionk * coq_Term
  | Coq_term_record of Coq_ty.recordi
     * (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Term) namedEnv

  val coq_NoConfusionPackage_Term :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (Coq_ty.coq_Ty * coq_Term) noConfusionPackage

  type coq_Term_sig = coq_Term

  val coq_Term_sig_pack :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> Coq_ty.coq_Ty * coq_Term

  val coq_Term_Signature :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> (coq_Term, Coq_ty.coq_Ty, coq_Term_sig) signature

  val term_enum :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.enumi
    -> Coq_ty.enumt -> coq_Term

  val term_list :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term list -> coq_Term

  val term_bvec :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term t -> coq_Term

  val term_relop_neg :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> coq_Term -> coq_Term -> coq_Term

  val term_truncate :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> coq_Term -> coq_Term

  val term_vector_subrange :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> nat -> coq_Term -> coq_Term

  val term_update_vector_subrange :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> nat -> coq_Term -> coq_Term -> coq_Term

  val coq_Term_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar ->
    Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Val -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1 -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty
    Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, coq_Term) Coq_env.coq_Env ->
    (Coq_ty.coq_Ty, coq_Term, 'a1) Coq_env.coq_All -> 'a1) -> (Coq_ty.unioni
    -> Coq_ty.unionk -> coq_Term -> 'a1 -> 'a1) -> (Coq_ty.recordi ->
    (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Term) namedEnv -> ((Coq_ty.recordf,
    Coq_ty.coq_Ty) Binding.coq_Binding, coq_Term, 'a1) Coq_env.coq_All ->
    'a1) -> Coq_ty.coq_Ty -> coq_Term -> 'a1

  val coq_Term_rec :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar ->
    Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Val -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1 -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty
    Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, coq_Term) Coq_env.coq_Env ->
    (Coq_ty.coq_Ty, coq_Term, 'a1) Coq_env.coq_All -> 'a1) -> (Coq_ty.unioni
    -> Coq_ty.unionk -> coq_Term -> 'a1 -> 'a1) -> (Coq_ty.recordi ->
    (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Term) namedEnv -> ((Coq_ty.recordf,
    Coq_ty.coq_Ty) Binding.coq_Binding, coq_Term, 'a1) Coq_env.coq_All ->
    'a1) -> Coq_ty.coq_Ty -> coq_Term -> 'a1

  val coq_Term_int_case :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (Coq_ty.coq_Val -> 'a1) -> (coq_Term -> coq_Term -> 'a1) -> (coq_Term ->
    coq_Term -> 'a1) -> (coq_Term -> coq_Term -> 'a1) -> (coq_Term ->
    coq_Term -> 'a1) -> (coq_Term -> 'a1) -> (nat -> coq_Term -> 'a1) -> (nat
    -> coq_Term -> 'a1) -> coq_Term -> 'a1

  val coq_Term_int_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (Coq_ty.coq_Val -> 'a1) -> (coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) ->
    (coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) -> (coq_Term -> coq_Term ->
    'a1 -> 'a1 -> 'a1) -> (coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) ->
    (coq_Term -> 'a1 -> 'a1) -> (nat -> coq_Term -> 'a1) -> (nat -> coq_Term
    -> 'a1) -> coq_Term -> 'a1

  val coq_Term_bool_case :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (Coq_ty.coq_Val -> 'a1) -> (coq_Term -> coq_Term -> 'a1) -> (coq_Term ->
    coq_Term -> 'a1) -> (Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> coq_Term ->
    coq_Term -> 'a1) -> (coq_Term -> 'a1) -> coq_Term -> 'a1

  val coq_Term_bool_ind :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (Coq_ty.coq_Val -> 'a1) -> (coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) ->
    (coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_bop.coq_RelOp -> coq_Term -> coq_Term -> 'a1) -> (coq_Term -> 'a1 ->
    'a1) -> coq_Term -> 'a1

  val coq_Term_list_case :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> (lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) -> (coq_Term ->
    coq_Term -> 'a1) -> (coq_Term -> coq_Term -> 'a1) -> (coq_Term -> 'a1) ->
    coq_Term -> 'a1

  val coq_Term_prod_case :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> (lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) ->
    (coq_Term -> coq_Term -> 'a1) -> coq_Term -> 'a1

  val coq_Term_sum_case :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> (lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) ->
    (coq_Term -> 'a1) -> (coq_Term -> 'a1) -> coq_Term -> 'a1

  val coq_Term_bvec_case :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (nat -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term
    -> coq_Term -> 'a1) -> (nat -> nat -> nat -> __ -> coq_Term -> coq_Term
    -> 'a1) -> (nat -> coq_Term -> 'a1) -> (nat -> coq_Term -> 'a1) -> (nat
    -> nat -> __ -> coq_Term -> 'a1) -> (nat -> nat -> __ -> coq_Term -> 'a1)
    -> (nat -> coq_Term -> 'a1) -> (nat -> nat -> __ -> coq_Term -> 'a1) ->
    (nat -> nat -> nat -> __ -> coq_Term -> 'a1) -> (nat -> nat -> coq_Term
    -> 'a1) -> (nat -> nat -> coq_Term -> 'a1) -> nat -> coq_Term -> 'a1

  val coq_Term_bvec_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (nat -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1 ->
    'a1 -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) -> (nat
    -> coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> 'a1 -> 'a1 -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1 ->
    'a1 -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) -> (nat
    -> nat -> coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) -> (nat -> nat -> coq_Term ->
    coq_Term -> 'a1 -> 'a1 -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1 ->
    'a1) -> (nat -> nat -> nat -> __ -> coq_Term -> coq_Term -> 'a1 -> 'a1 ->
    'a1) -> (nat -> coq_Term -> 'a1 -> 'a1) -> (nat -> coq_Term -> 'a1 ->
    'a1) -> (nat -> nat -> __ -> coq_Term -> 'a1 -> 'a1) -> (nat -> nat -> __
    -> coq_Term -> 'a1 -> 'a1) -> (nat -> coq_Term -> 'a1) -> (nat -> nat ->
    __ -> coq_Term -> 'a1 -> 'a1) -> (nat -> nat -> nat -> __ -> coq_Term ->
    'a1 -> 'a1) -> (nat -> nat -> coq_Term -> 'a1 -> 'a1) -> (nat -> nat ->
    coq_Term -> 'a1 -> 'a1) -> nat -> coq_Term -> 'a1

  val coq_Term_tuple_case :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) ->
    ((Coq_ty.coq_Ty, coq_Term) Coq_env.coq_Env -> 'a1) -> coq_Term -> 'a1

  val coq_Term_union_case :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.unioni -> (lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) -> (Coq_ty.unionk ->
    coq_Term -> 'a1) -> coq_Term -> 'a1

  val coq_Term_record_case :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.recordi -> (lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) -> ((Coq_ty.recordf,
    Coq_ty.coq_Ty, coq_Term) namedEnv -> 'a1) -> coq_Term -> 'a1

  type coq_ListView =
  | Coq_term_list_var of lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_term_list_val of Coq_ty.coq_Val
  | Coq_term_list_cons of coq_Term * coq_Term * coq_ListView
  | Coq_term_list_append of coq_Term * coq_Term * coq_ListView * coq_ListView
  | Coq_term_list_rev of coq_Term * coq_ListView

  val coq_ListView_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> (lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) -> (coq_Term ->
    coq_Term -> coq_ListView -> 'a1 -> 'a1) -> (coq_Term -> coq_Term ->
    coq_ListView -> 'a1 -> coq_ListView -> 'a1 -> 'a1) -> (coq_Term ->
    coq_ListView -> 'a1 -> 'a1) -> coq_Term -> coq_ListView -> 'a1

  val coq_ListView_rec :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> (lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Val -> 'a1) -> (coq_Term ->
    coq_Term -> coq_ListView -> 'a1 -> 'a1) -> (coq_Term -> coq_Term ->
    coq_ListView -> 'a1 -> coq_ListView -> 'a1 -> 'a1) -> (coq_Term ->
    coq_ListView -> 'a1 -> 'a1) -> coq_Term -> coq_ListView -> 'a1

  type coq_View = __

  val view_var :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar ->
    Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> coq_View

  val view_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Val -> coq_View

  val view_binop :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> coq_View -> coq_View -> coq_View

  val view_unop :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    coq_View -> coq_View

  val view :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> coq_View

  val coq_Term_eqb_clause_3 :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (Coq_ty.coq_Ty -> coq_Term -> coq_Term -> bool) -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    sumbool -> coq_Term -> coq_Term -> bool

  val coq_Term_eqb_clause_4 :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (Coq_ty.coq_Ty -> coq_Term -> coq_Term -> bool) -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> sumbool -> coq_Term -> bool

  val coq_Term_eqb_clause_6 :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (Coq_ty.coq_Ty -> coq_Term -> coq_Term -> bool) -> Coq_ty.unioni ->
    Coq_ty.unionk -> coq_Term -> Coq_ty.unionk -> sumbool -> coq_Term -> bool

  val coq_Term_eqb :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> coq_Term -> bool

  val coq_Term_eqb_spec :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> coq_Term -> reflect

  type 'a coq_List = 'a list

  type 'a coq_Const = 'a

  type coq_Sub =
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding, coq_Term) Coq_env.coq_Env

  type 't coq_Subst =
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 't -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub -> 't

  val subst :
    'a1 coq_Subst -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_Sub -> 'a1

  val sub_term :
    Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_Term -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_Sub -> coq_Term

  val coq_SubstTerm : Coq_ty.coq_Ty -> coq_Term coq_Subst

  val coq_SubstList : 'a1 coq_Subst -> 'a1 coq_List coq_Subst

  val coq_SubstConst : 'a1 coq_Const coq_Subst

  val coq_SubstEnv :
    ('a1 -> 'a2 coq_Subst) -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2)
    Coq_env.coq_Env coq_Subst

  val sub_id :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub

  val sub_snoc :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_Term -> coq_Sub

  val sub_shift :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_Sub

  val sub_wk1 :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_Sub

  val sub_cat_left :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub

  val sub_cat_right :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub

  val sub_up1 :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_Sub

  val sub_up :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub

  val sub_single :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_Term -> coq_Sub

  type 't coq_SubstLaws =
  | Build_SubstLaws

  val coq_SubstLawsTerm : Coq_ty.coq_Ty -> coq_Term coq_SubstLaws

  val coq_SubstLawsList :
    'a1 coq_Subst -> 'a1 coq_SubstLaws -> 'a1 coq_List coq_SubstLaws

  val coq_SubstLawsConst : 'a1 coq_Const coq_SubstLaws

  val coq_SubstLawsEnv :
    ('a1 -> 'a2 coq_Subst) -> ('a1 -> 'a2 coq_SubstLaws) -> 'a1
    Coq_ctx.coq_Ctx -> ('a1, 'a2) Coq_env.coq_Env coq_SubstLaws

  val subst_ctx : 'a1 coq_Subst -> 'a1 Coq_ctx.coq_Ctx coq_Subst

  val substlaws_ctx :
    'a1 coq_Subst -> 'a1 coq_SubstLaws -> 'a1 Coq_ctx.coq_Ctx coq_SubstLaws

  module SubNotations :
   sig
   end

  type ('a, 'b) coq_Pair = ('a, 'b) prod

  val coq_SubstPair :
    'a1 coq_Subst -> 'a2 coq_Subst -> ('a1, 'a2) coq_Pair coq_Subst

  val coq_SubstLawsPair :
    'a1 coq_Subst -> 'a1 coq_SubstLaws -> 'a2 coq_Subst -> 'a2 coq_SubstLaws
    -> ('a1, 'a2) coq_Pair coq_SubstLaws

  type 'a coq_Option = 'a option

  val coq_SubstOption : 'a1 coq_Subst -> 'a1 coq_Option coq_Subst

  val coq_SubstLawsOption :
    'a1 coq_Subst -> 'a1 coq_SubstLaws -> 'a1 coq_Option coq_SubstLaws

  type coq_Unit = unit0

  val coq_SubstUnit : coq_Unit coq_Subst

  val coq_SubstLawsUnit : coq_Unit coq_SubstLaws

  type coq_SStore = (pVar, Coq_ty.coq_Ty, coq_Term) namedEnv

  val subst_localstore :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SStore
    coq_Subst

  val substlaws_localstore :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SStore
    coq_SubstLaws

  module TermNotations :
   sig
   end

  type coq_ETerm =
  | Coq_eterm_var of lVar * Coq_ty.coq_Ty * nat
  | Coq_eterm_val of Coq_ty.coq_Ty * Coq_ty.coq_Val
  | Coq_eterm_binop of Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_ETerm * coq_ETerm
  | Coq_eterm_unop of Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_ETerm
  | Coq_eterm_tuple of Coq_ty.coq_Ty Coq_ctx.coq_Ctx
     * (Coq_ty.coq_Ty, coq_ETerm) Coq_env.coq_Env
  | Coq_eterm_union of Coq_ty.unioni * Coq_ty.unionk * coq_ETerm
  | Coq_eterm_record of Coq_ty.recordi
     * (Coq_ty.recordf, Coq_ty.coq_Ty, coq_ETerm) namedEnv

  val erase_term :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> coq_ETerm

  val erase_SStore :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SStore ->
    (pVar, Coq_ty.coq_Ty, coq_ETerm) namedEnv

  type 'n coq_TuplePat =
  | Coq_tuplepat_nil
  | Coq_tuplepat_snoc of Coq_ty.coq_Ty Coq_ctx.coq_Ctx
     * ('n, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * 'n coq_TuplePat * Coq_ty.coq_Ty * 'n

  val coq_TuplePat_rect :
    'a2 -> (Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> 'a2 ->
    Coq_ty.coq_Ty -> 'a1 -> 'a2) -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat ->
    'a2

  val coq_TuplePat_rec :
    'a2 -> (Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> 'a2 ->
    Coq_ty.coq_Ty -> 'a1 -> 'a2) -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat ->
    'a2

  type 'n coq_RecordPat =
  | Coq_recordpat_nil
  | Coq_recordpat_snoc of (Coq_ty.recordf, Coq_ty.coq_Ty) Binding.coq_Binding
                          Coq_ctx.coq_Ctx
     * ('n, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * 'n coq_RecordPat * Coq_ty.recordf * Coq_ty.coq_Ty * 'n

  val coq_RecordPat_rect :
    'a2 -> ((Coq_ty.recordf, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> 'a2 -> Coq_ty.recordf ->
    Coq_ty.coq_Ty -> 'a1 -> 'a2) -> (Coq_ty.recordf, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> 'a2

  val coq_RecordPat_rec :
    'a2 -> ((Coq_ty.recordf, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> 'a2 -> Coq_ty.recordf ->
    Coq_ty.coq_Ty -> 'a1 -> 'a2) -> (Coq_ty.recordf, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> 'a2

  val tuple_pattern_match_env :
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> (Coq_ty.coq_Ty, 'a2)
    Coq_env.coq_Env -> ('a1, Coq_ty.coq_Ty, 'a2) namedEnv

  val tuple_pattern_match_env_reverse :
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> ('a1, Coq_ty.coq_Ty, 'a2) namedEnv
    -> (Coq_ty.coq_Ty, 'a2) Coq_env.coq_Env

  val tuple_pattern_match_val :
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> Coq_ty.coq_Val -> ('a1,
    Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv

  val record_pattern_match_env :
    (Coq_ty.recordf, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1
    coq_RecordPat -> (Coq_ty.recordf, Coq_ty.coq_Ty, 'a2) namedEnv -> ('a1,
    Coq_ty.coq_Ty, 'a2) namedEnv

  val record_pattern_match_env_reverse :
    (Coq_ty.recordf, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1
    coq_RecordPat -> ('a1, Coq_ty.coq_Ty, 'a2) namedEnv -> (Coq_ty.recordf,
    Coq_ty.coq_Ty, 'a2) namedEnv

  val record_pattern_match_val :
    Coq_ty.recordi -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> Coq_ty.coq_Val -> ('a1,
    Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv

  type 'n coq_Pattern =
  | Coq_pat_var of 'n * Coq_ty.coq_Ty
  | Coq_pat_bool
  | Coq_pat_list of Coq_ty.coq_Ty * 'n * 'n
  | Coq_pat_pair of 'n * 'n * Coq_ty.coq_Ty * Coq_ty.coq_Ty
  | Coq_pat_sum of Coq_ty.coq_Ty * Coq_ty.coq_Ty * 'n * 'n
  | Coq_pat_unit
  | Coq_pat_enum of Coq_ty.enumi
  | Coq_pat_bvec_split of nat * nat * 'n * 'n
  | Coq_pat_bvec_exhaustive of nat
  | Coq_pat_tuple of Coq_ty.coq_Ty Coq_ctx.coq_Ctx
     * ('n, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * 'n coq_TuplePat
  | Coq_pat_record of Coq_ty.recordi
     * ('n, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * 'n coq_RecordPat
  | Coq_pat_union of Coq_ty.unioni * (Coq_ty.unionk -> 'n coq_Pattern)

  val coq_Pattern_rect :
    ('a1 -> Coq_ty.coq_Ty -> 'a2) -> 'a2 -> (Coq_ty.coq_Ty -> 'a1 -> 'a1 ->
    'a2) -> ('a1 -> 'a1 -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> 'a2) ->
    (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> 'a1 -> 'a1 -> 'a2) -> 'a2 ->
    (Coq_ty.enumi -> 'a2) -> (nat -> nat -> 'a1 -> 'a1 -> 'a2) -> (nat ->
    'a2) -> (Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> 'a2) ->
    (Coq_ty.recordi -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> 'a2) -> (Coq_ty.unioni ->
    (Coq_ty.unionk -> 'a1 coq_Pattern) -> (Coq_ty.unionk -> 'a2) -> 'a2) ->
    Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a2

  val coq_Pattern_rec :
    ('a1 -> Coq_ty.coq_Ty -> 'a2) -> 'a2 -> (Coq_ty.coq_Ty -> 'a1 -> 'a1 ->
    'a2) -> ('a1 -> 'a1 -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> 'a2) ->
    (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> 'a1 -> 'a1 -> 'a2) -> 'a2 ->
    (Coq_ty.enumi -> 'a2) -> (nat -> nat -> 'a1 -> 'a1 -> 'a2) -> (nat ->
    'a2) -> (Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> 'a2) ->
    (Coq_ty.recordi -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> 'a2) -> (Coq_ty.unioni ->
    (Coq_ty.unionk -> 'a1 coq_Pattern) -> (Coq_ty.unionk -> 'a2) -> 'a2) ->
    Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a2

  type 'n coq_PatternCase = __

  val coq_EqDec_PatternCase :
    Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1 coq_PatternCase eqDec

  val coq_Finite_PatternCase :
    Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1 coq_PatternCase finite

  val coq_PatternCaseCtx :
    Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1 coq_PatternCase -> ('a1,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  type 'n coq_MatchResult =
    ('n coq_PatternCase, ('n, Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv) sigT

  val pattern_match_val :
    Coq_ty.coq_Ty -> 'a1 coq_Pattern -> Coq_ty.coq_Val -> 'a1 coq_MatchResult

  val pattern_match_val_reverse :
    Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1 coq_PatternCase -> ('a1,
    Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv -> Coq_ty.coq_Val

  val pattern_match_val_reverse' :
    Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1 coq_MatchResult -> Coq_ty.coq_Val

  type ('n, 'r) coq_PatternCaseCurried = __

  val of_pattern_case_curried :
    ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty
    -> 'a1 coq_Pattern -> ('a1, 'a2) coq_PatternCaseCurried -> 'a1
    coq_PatternCase -> 'a2

  type ('n, 'r) coq_Alternative = { alt_pat : 'n coq_Pattern;
                                    alt_rhs : ('n, 'r) coq_PatternCaseCurried }

  val alt_pat :
    ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty
    -> ('a1, 'a2) coq_Alternative -> 'a1 coq_Pattern

  val alt_rhs :
    ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty
    -> ('a1, 'a2) coq_Alternative -> ('a1, 'a2) coq_PatternCaseCurried

  val freshen_ctx :
    ('a1 -> lVar) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val unfreshen_namedenv :
    ('a1 -> lVar) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty, 'a2) namedEnv -> ('a1,
    Coq_ty.coq_Ty, 'a2) namedEnv

  val freshen_namedenv :
    ('a1 -> lVar) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty, 'a2) namedEnv -> (lVar,
    Coq_ty.coq_Ty, 'a2) namedEnv

  val freshen_tuplepat :
    ('a1 -> lVar) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 coq_TuplePat -> lVar
    coq_TuplePat

  val freshen_recordpat :
    ('a1 -> lVar) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (Coq_ty.recordf, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_RecordPat -> lVar coq_RecordPat

  val freshen_pattern :
    ('a1 -> lVar) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> lVar coq_Pattern

  val unfreshen_patterncase :
    ('a1 -> lVar) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> lVar
    coq_PatternCase -> 'a1 coq_PatternCase

  val freshen_patterncase :
    ('a1 -> lVar) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1
    coq_PatternCase -> lVar coq_PatternCase

  val unfreshen_patterncaseenv' :
    ('a1 -> lVar) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> lVar
    coq_PatternCase -> (lVar, Coq_ty.coq_Ty, 'a2) namedEnv -> ('a1,
    Coq_ty.coq_Ty, 'a2) namedEnv

  val freshen_patterncaseenv :
    ('a1 -> lVar) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1
    coq_PatternCase -> ('a1, Coq_ty.coq_Ty, 'a2) namedEnv -> (lVar,
    Coq_ty.coq_Ty, 'a2) namedEnv

  val unfreshen_patterncaseenv :
    ('a1 -> lVar) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> lVar
    coq_PatternCase -> (lVar, Coq_ty.coq_Ty, 'a2) namedEnv -> ('a1,
    Coq_ty.coq_Ty, 'a2) namedEnv

  val freshen_matchresult :
    ('a1 -> lVar) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1
    coq_MatchResult -> lVar coq_MatchResult

  val unfreshen_matchresult :
    ('a1 -> lVar) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 coq_Pattern -> lVar
    coq_MatchResult -> 'a1 coq_MatchResult

  type 't coq_OccursCheck =
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 't -> 't option

  val occurs_check :
    'a1 coq_OccursCheck -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1 -> 'a1 option

  val coq_OccursCheck_Const : 'a1 coq_Const coq_OccursCheck

  val occurs_check_env :
    ('a1 -> 'a2 coq_OccursCheck) -> 'a1 Coq_ctx.coq_Ctx -> ('a1, 'a2)
    Coq_env.coq_Env coq_OccursCheck

  val occurs_check_term : Coq_ty.coq_Ty -> coq_Term coq_OccursCheck

  val occurs_check_list : 'a1 coq_OccursCheck -> 'a1 coq_List coq_OccursCheck

  val occurs_check_sub :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Sub
    coq_OccursCheck

  val occurs_check_pair :
    'a1 coq_OccursCheck -> 'a2 coq_OccursCheck -> ('a1, 'a2) coq_Pair
    coq_OccursCheck

  val occurs_check_option :
    'a1 coq_OccursCheck -> 'a1 coq_Option coq_OccursCheck

  val occurs_check_unit : coq_Unit coq_OccursCheck

  val occurscheck_ctx :
    'a1 coq_OccursCheck -> 'a1 Coq_ctx.coq_Ctx coq_OccursCheck

  module Experimental :
   sig
    type 't coq_OccursCheckView =
    | Succ of 't
    | Fail of 't

    val coq_OccursCheckView_rect :
      'a1 coq_Subst -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> ('a1 -> 'a2) ->
      ('a1 -> 'a2) -> 'a1 -> 'a1 coq_OccursCheckView -> 'a2

    val coq_OccursCheckView_rec :
      'a1 coq_Subst -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> ('a1 -> 'a2) ->
      ('a1 -> 'a2) -> 'a1 -> 'a1 coq_OccursCheckView -> 'a2

    type 't coq_OccursCheck =
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> 't -> 't coq_OccursCheckView

    val occurs_check_view :
      'a1 coq_Subst -> 'a1 coq_OccursCheck -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> 'a1 -> 'a1 coq_OccursCheckView

    val coq_OccursCheckEnv :
      ('a1 -> 'a2 coq_Subst) -> ('a1 -> 'a2 coq_OccursCheck) -> 'a1
      Coq_ctx.coq_Ctx -> ('a1, 'a2) Coq_env.coq_Env coq_OccursCheck
   end

  type 'sb coq_SubstUniv = { initSU : ((lVar, Coq_ty.coq_Ty)
                                      Binding.coq_Binding Coq_ctx.coq_Ctx ->
                                      'sb);
                             transSU : ((lVar, Coq_ty.coq_Ty)
                                       Binding.coq_Binding Coq_ctx.coq_Ctx ->
                                       (lVar, Coq_ty.coq_Ty)
                                       Binding.coq_Binding Coq_ctx.coq_Ctx ->
                                       (lVar, Coq_ty.coq_Ty)
                                       Binding.coq_Binding Coq_ctx.coq_Ctx ->
                                       'sb -> 'sb -> 'sb);
                             interpSU : ((lVar, Coq_ty.coq_Ty)
                                        Binding.coq_Binding Coq_ctx.coq_Ctx
                                        -> (lVar, Coq_ty.coq_Ty)
                                        Binding.coq_Binding Coq_ctx.coq_Ctx
                                        -> 'sb -> coq_Sub) }

  val initSU :
    'a1 coq_SubstUniv -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1

  val transSU :
    'a1 coq_SubstUniv -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 -> 'a1 -> 'a1

  val interpSU :
    'a1 coq_SubstUniv -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 -> coq_Sub

  type ('sb, 't) coq_SubstSU =
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 't -> 'sb -> 't

  val substSU :
    ('a1, 'a2) coq_SubstSU -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a2 -> 'a1 -> 'a2

  val substSU_term :
    'a1 coq_SubstUniv -> Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term -> 'a1 -> coq_Term

  val coq_SubstSUTerm :
    'a1 coq_SubstUniv -> Coq_ty.coq_Ty -> ('a1, coq_Term) coq_SubstSU

  val substSU_option :
    ('a1, 'a2) coq_SubstSU -> ('a1, 'a2 coq_Option) coq_SubstSU

  type 'sb coq_MeetResult = { _UU03a3_12 : (lVar, Coq_ty.coq_Ty)
                                           Binding.coq_Binding Coq_ctx.coq_Ctx;
                              meetLeft : 'sb; meetRight : 'sb; meetUp : 
                              'sb }

  val _UU03a3_12 :
    'a1 coq_SubstUniv -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_MeetResult -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx

  val meetLeft :
    'a1 coq_SubstUniv -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_MeetResult -> 'a1

  val meetRight :
    'a1 coq_SubstUniv -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_MeetResult -> 'a1

  val meetUp :
    'a1 coq_SubstUniv -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 coq_MeetResult -> 'a1

  type 'sb coq_SubstUnivMeet =
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'sb -> 'sb -> 'sb
    coq_MeetResult

  val meetSU :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 -> 'a1 -> 'a1 coq_MeetResult

  val coq_SubstSU_env :
    'a1 coq_SubstUniv -> 'a2 Coq_ctx.coq_Ctx -> ('a2 -> ('a1, 'a3)
    coq_SubstSU) -> ('a1, ('a2, 'a3) Coq_env.coq_Env) coq_SubstSU

  val coq_SubstSU_sub :
    'a1 coq_SubstUniv -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, coq_Sub) coq_SubstSU

  val substSU_pair :
    ('a1, 'a2) coq_SubstSU -> ('a1, 'a3) coq_SubstSU -> ('a1, ('a2, 'a3)
    coq_Pair) coq_SubstSU

  val substSU_list : ('a1, 'a2) coq_SubstSU -> ('a1, 'a2 coq_List) coq_SubstSU

  val substSU_Const : ('a1, 'a2 coq_Const) coq_SubstSU

  type 'sb coq_SubstUnivVar =
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'sb

  val suVar :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUnivVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1

  type 'sb coq_SubstUnivVarUp =
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> 'sb -> 'sb

  val upSU :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUnivVar -> 'a1
    coq_SubstUnivVarUp -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> 'a1 -> 'a1

  type 'sb coq_SubstUnivVarDown = { wkVarSU : ((lVar, Coq_ty.coq_Ty)
                                              Binding.coq_Binding
                                              Coq_ctx.coq_Ctx -> (lVar,
                                              Coq_ty.coq_Ty)
                                              Binding.coq_Binding
                                              Coq_ctx.coq_Ctx -> (lVar,
                                              Coq_ty.coq_Ty)
                                              Binding.coq_Binding -> (lVar,
                                              Coq_ty.coq_Ty)
                                              Binding.coq_Binding
                                              Coq_ctx.coq_In -> 'sb -> (lVar,
                                              Coq_ty.coq_Ty)
                                              Binding.coq_Binding
                                              Coq_ctx.coq_In);
                                    downSU : ((lVar, Coq_ty.coq_Ty)
                                             Binding.coq_Binding
                                             Coq_ctx.coq_Ctx -> (lVar,
                                             Coq_ty.coq_Ty)
                                             Binding.coq_Binding
                                             Coq_ctx.coq_Ctx -> (lVar,
                                             Coq_ty.coq_Ty)
                                             Binding.coq_Binding -> (lVar,
                                             Coq_ty.coq_Ty)
                                             Binding.coq_Binding
                                             Coq_ctx.coq_In -> 'sb -> 'sb) }

  val wkVarSU :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUnivVar -> 'a1
    coq_SubstUnivVarDown -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1 -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In

  val downSU :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUnivVar -> 'a1
    coq_SubstUnivVarDown -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1 -> 'a1

  type ('sb, 't) coq_BoxSb = { unboxSb : ((lVar, Coq_ty.coq_Ty)
                                         Binding.coq_Binding Coq_ctx.coq_Ctx
                                         -> 'sb -> 't) }

  val unboxSb :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, 'a2)
    coq_BoxSb -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    'a1 -> 'a2

  val boxSb :
    ('a1, 'a2) coq_SubstSU -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a2 -> ('a1, 'a2) coq_BoxSb

  val substSU_BoxSb :
    ('a1, 'a2) coq_SubstSU -> 'a1 coq_SubstUniv -> ('a1, ('a1, 'a2)
    coq_BoxSb) coq_SubstSU

  type ('sb, 't) coq_Weakened = { _UU03a3_supp : (lVar, Coq_ty.coq_Ty)
                                                 Binding.coq_Binding
                                                 Coq_ctx.coq_Ctx;
                                  embedSupport : 'sb;
                                  wkVal : ('sb, 't) coq_BoxSb }

  val _UU03a3_supp :
    'a1 coq_SubstUniv -> ('a1, 'a2) coq_SubstSU -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Weakened -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  val embedSupport :
    'a1 coq_SubstUniv -> ('a1, 'a2) coq_SubstSU -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Weakened -> 'a1

  val wkVal :
    'a1 coq_SubstUniv -> ('a1, 'a2) coq_SubstSU -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_Weakened -> ('a1,
    'a2) coq_BoxSb

  val unWeaken :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1
    coq_SubstUniv -> ('a1, 'a2) coq_SubstSU -> ('a1, 'a2) coq_Weakened -> 'a2

  val liftBoxUnOp :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 -> 'a2)
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a3,
    'a1) coq_BoxSb -> ('a3, 'a2) coq_BoxSb

  val liftBoxBinOp :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 -> 'a2
    -> 'a3) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    ('a4, 'a1) coq_BoxSb -> ('a4, 'a2) coq_BoxSb -> ('a4, 'a3) coq_BoxSb

  val weakenInit :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> ('a1, 'a2) coq_SubstSU ->
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a2 -> ('a1, 'a2) coq_Weakened

  type ('sb, 't) coq_GenOccursCheck =
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 't -> ('sb,
    't) coq_Weakened

  val gen_occurs_check :
    'a1 coq_SubstUniv -> ('a1, 'a2) coq_SubstSU -> ('a1, 'a2)
    coq_GenOccursCheck -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a2 -> ('a1, 'a2) coq_Weakened

  val coq_GenOccursCheck_Const :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> ('a1, 'a2 coq_Const) coq_GenOccursCheck

  val liftUnOp :
    'a1 coq_SubstUniv -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_SubstSU -> ('a1, 'a3) coq_SubstSU ->
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a2 -> 'a3)
    -> ('a1, 'a2) coq_Weakened -> ('a1, 'a3) coq_Weakened

  val liftBinOp :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_SubstSU -> ('a1, 'a3) coq_SubstSU ->
    ('a1, 'a4) coq_SubstSU -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a2 -> 'a3 -> 'a4) -> ('a1, 'a2) coq_Weakened -> ('a1,
    'a3) coq_Weakened -> ('a1, 'a4) coq_Weakened

  val liftTernOp :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> ('a1, 'a2) coq_SubstSU -> ('a1, 'a3) coq_SubstSU ->
    ('a1, 'a4) coq_SubstSU -> ('a1, 'a5) coq_SubstSU -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a2 -> 'a3 -> 'a4
    -> 'a5) -> ('a1, 'a2) coq_Weakened -> ('a1, 'a3) coq_Weakened -> ('a1,
    'a4) coq_Weakened -> ('a1, 'a5) coq_Weakened

  val gen_occurs_check_env :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> ('a2 -> ('a1, 'a3) coq_SubstSU) -> ('a2 -> ('a1,
    'a3) coq_GenOccursCheck) -> 'a2 Coq_ctx.coq_Ctx -> ('a1, ('a2, 'a3)
    Coq_env.coq_Env) coq_GenOccursCheck

  val gen_occurs_check_term :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUnivVar -> 'a1
    coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> Coq_ty.coq_Ty -> ('a1, coq_Term) coq_GenOccursCheck

  val gen_occurs_check_list :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> ('a1, 'a2) coq_SubstSU -> ('a1, 'a2)
    coq_GenOccursCheck -> ('a1, 'a2 coq_List) coq_GenOccursCheck

  val gen_occurs_check_pair :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> ('a1, 'a2) coq_SubstSU -> ('a1, 'a3) coq_SubstSU ->
    ('a1, 'a2) coq_GenOccursCheck -> ('a1, 'a3) coq_GenOccursCheck -> ('a1,
    ('a2, 'a3) coq_Pair) coq_GenOccursCheck

  val gen_occurs_check_option :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> ('a1, 'a2) coq_SubstSU -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> ('a1, 'a2) coq_GenOccursCheck -> ('a1, 'a2
    coq_Option) coq_GenOccursCheck

  val substSU_ctx :
    ('a1, 'a2) coq_SubstSU -> ('a1, 'a2 Coq_ctx.coq_Ctx) coq_SubstSU

  val gen_occurscheck_ctx :
    ('a1, 'a2) coq_SubstSU -> 'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet ->
    ('a1, 'a2) coq_GenOccursCheck -> ('a1, 'a2 Coq_ctx.coq_Ctx)
    coq_GenOccursCheck

  val gen_occurs_check_unit :
    'a1 coq_SubstUniv -> 'a1 coq_SubstUnivMeet -> 'a1 coq_SubstUniv -> 'a1
    coq_SubstUnivMeet -> ('a1, coq_Unit) coq_GenOccursCheck

  type coq_WeakensTo =
  | WkNil
  | WkSkipVar of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding * coq_WeakensTo
  | WkKeepVar of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding * coq_WeakensTo

  val coq_WeakensTo_rect :
    'a1 -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1 -> 'a1) ->
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1 -> 'a1) ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> 'a1

  val coq_WeakensTo_rec :
    'a1 -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1 -> 'a1) ->
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1 -> 'a1) ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> 'a1

  val wkRefl :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo

  val wk1 :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo

  val interpWk :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_Sub

  val transWk :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakensTo -> coq_WeakensTo

  type transWk_graph =
  | Coq_transWk_graph_equation_1
  | Coq_transWk_graph_equation_2 of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
                                    Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding * coq_WeakensTo
     * coq_WeakensTo * transWk_graph
  | Coq_transWk_graph_equation_3 of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
                                    Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo * coq_WeakensTo * transWk_graph
  | Coq_transWk_graph_equation_4 of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
                                    Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo * coq_WeakensTo * transWk_graph

  val transWk_graph_rect :
    'a1 -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> coq_WeakensTo ->
    transWk_graph -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo -> transWk_graph -> 'a1
    -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    transWk_graph -> 'a1 -> 'a1) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo -> coq_WeakensTo ->
    transWk_graph -> 'a1

  val transWk_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakensTo -> transWk_graph

  val transWk_elim :
    'a1 -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> coq_WeakensTo ->
    'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    'a1 -> 'a1) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakensTo -> 'a1

  val coq_FunctionalElimination_transWk :
    __ -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> coq_WeakensTo ->
    __ -> __) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    __ -> __) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    __ -> __) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakensTo -> __

  val coq_FunctionalInduction_transWk :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakensTo -> coq_WeakensTo) functionalInduction

  val wkNilInit :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo

  val wkKeepCtx :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo

  type coq_WeakenZeroView =
  | VarUnused of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo
  | VarUsed of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo

  val coq_WeakenZeroView_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> 'a1) -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    'a1) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakenZeroView -> 'a1

  val coq_WeakenZeroView_rec :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> 'a1) -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    'a1) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakenZeroView -> 'a1

  val weakenZeroView :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> coq_WeakenZeroView

  type weakenZeroView_graph =
  | Coq_weakenZeroView_graph_equation_1 of (lVar, Coq_ty.coq_Ty)
                                           Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding * coq_WeakensTo
  | Coq_weakenZeroView_graph_equation_2 of (lVar, Coq_ty.coq_Ty)
                                           Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo

  val weakenZeroView_graph_rect :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1) -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> 'a1) -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> coq_WeakenZeroView
    -> weakenZeroView_graph -> 'a1

  val weakenZeroView_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
    weakenZeroView_graph

  val weakenZeroView_elim :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1) -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> 'a1) -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1

  val coq_FunctionalElimination_weakenZeroView :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> __) -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> __) -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> __

  val coq_FunctionalInduction_weakenZeroView :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo ->
    coq_WeakenZeroView) functionalInduction

  type coq_WeakenNilView =
  | WkNilViewNil

  val coq_WeakenNilView_rect :
    'a1 -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakenNilView -> 'a1

  val coq_WeakenNilView_rec :
    'a1 -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakenNilView -> 'a1

  val weakenNilView :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakenNilView

  type weakenNilView_graph =
  | Coq_weakenNilView_graph_equation_1

  val weakenNilView_graph_rect :
    'a1 -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakenNilView -> weakenNilView_graph -> 'a1

  val weakenNilView_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> weakenNilView_graph

  val weakenNilView_elim :
    'a1 -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> 'a1

  val coq_FunctionalElimination_weakenNilView :
    __ -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> __

  val coq_FunctionalInduction_weakenNilView :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakenNilView) functionalInduction

  val wkRemove :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo

  val wkSingleton :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo

  val wkVarZeroIn :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In

  type wkVarZeroIn_graph =
  | Coq_wkVarZeroIn_graph_equation_1 of (lVar, Coq_ty.coq_Ty)
                                        Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding * coq_WeakensTo
     * wkVarZeroIn_graph
  | Coq_wkVarZeroIn_graph_equation_2 of (lVar, Coq_ty.coq_Ty)
                                        Binding.coq_Binding
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo

  val wkVarZeroIn_graph_rect :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> coq_WeakensTo -> wkVarZeroIn_graph -> 'a1 -> 'a1)
    -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> 'a1) -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> wkVarZeroIn_graph ->
    'a1

  val wkVarZeroIn_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> wkVarZeroIn_graph

  val wkVarZeroIn_elim :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> coq_WeakensTo -> 'a1 -> 'a1) -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> 'a1) -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> 'a1

  val coq_FunctionalElimination_wkVarZeroIn :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> coq_WeakensTo -> __ -> __) -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> __) -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> __

  val coq_FunctionalInduction_wkVarZeroIn :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In) functionalInduction

  val weakenIn :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In

  val weakenRemovePres :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo

  type coq_WeakenRemoveView =
  | MkWeakenRemoveView of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
                          Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * coq_WeakensTo

  val coq_WeakenRemoveView_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo -> 'a1) -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo ->
    coq_WeakenRemoveView -> 'a1

  val coq_WeakenRemoveView_rec :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo -> 'a1) -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo ->
    coq_WeakenRemoveView -> 'a1

  val weakenRemoveView :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakenRemoveView

  type coq_WeakenVarView =
  | WeakenVarUnused of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
                       Coq_ctx.coq_Ctx
     * coq_WeakensTo
  | WeakenVarUsed of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * coq_WeakensTo

  val coq_WeakenVarView_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> 'a1) -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo ->
    'a1) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakenVarView -> 'a1

  val coq_WeakenVarView_rec :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> 'a1) -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo ->
    'a1) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_WeakensTo -> coq_WeakenVarView -> 'a1

  val weakenVarView_obligations_obligation_1 :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> coq_WeakenVarView

  val weakenVarView_obligations_obligation_2 :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo -> coq_WeakenVarView)
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakenVarView

  val weakenVarView_obligations_obligation_3 :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo -> coq_WeakenVarView)
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakenVarView

  val weakenVarView :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo -> coq_WeakenVarView

  type weakenVarView_graph =
  | Coq_weakenVarView_graph_equation_1 of (lVar, Coq_ty.coq_Ty)
                                          Binding.coq_Binding
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_weakenVarView_graph_equation_2 of (lVar, Coq_ty.coq_Ty)
                                          Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * coq_WeakensTo
     * ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
       Binding.coq_Binding Coq_ctx.coq_In -> weakenVarView_graph)
  | Coq_weakenVarView_graph_equation_3 of (lVar, Coq_ty.coq_Ty)
                                          Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * coq_WeakensTo
     * ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
       Binding.coq_Binding Coq_ctx.coq_In -> weakenVarView_graph)

  val weakenVarView_graph_rect :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo
    -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> weakenVarView_graph) -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> 'a1) -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> coq_WeakensTo -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> weakenVarView_graph) -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> 'a1) -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> coq_WeakensTo -> coq_WeakenVarView ->
    weakenVarView_graph -> 'a1

  val weakenVarView_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo -> weakenVarView_graph

  val weakenVarView_elim :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo
    -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> 'a1) -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> coq_WeakensTo -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> 'a1) -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> coq_WeakensTo -> 'a1

  val coq_FunctionalElimination_weakenVarView :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo
    -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> __) -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> coq_WeakensTo -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> __) -> __) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo -> __

  val coq_FunctionalInduction_weakenVarView :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo -> coq_WeakenVarView)
    functionalInduction

  val substUniv_weaken : coq_WeakensTo coq_SubstUniv

  val extendMeetSkipSkip :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo coq_MeetResult ->
    coq_WeakensTo coq_MeetResult

  val extendMeetSkipKeep :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo coq_MeetResult ->
    coq_WeakensTo coq_MeetResult

  val extendMeetKeepSkip :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo coq_MeetResult ->
    coq_WeakensTo coq_MeetResult

  val extendMeetKeepKeep :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo coq_MeetResult ->
    coq_WeakensTo coq_MeetResult

  val meetWk :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakensTo -> coq_WeakensTo coq_MeetResult

  type meetWk_graph =
  | Coq_meetWk_graph_equation_1
  | Coq_meetWk_graph_equation_2 of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
                                   Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding * coq_WeakensTo
     * coq_WeakensTo * meetWk_graph
  | Coq_meetWk_graph_equation_3 of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
                                   Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo * coq_WeakensTo * meetWk_graph
  | Coq_meetWk_graph_equation_4 of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
                                   Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo * coq_WeakensTo * meetWk_graph
  | Coq_meetWk_graph_equation_5 of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
                                   Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_WeakensTo * coq_WeakensTo * meetWk_graph

  val meetWk_graph_rect :
    'a1 -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> coq_WeakensTo ->
    meetWk_graph -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakensTo -> meetWk_graph -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo -> meetWk_graph -> 'a1
    -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    meetWk_graph -> 'a1 -> 'a1) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo -> coq_WeakensTo
    coq_MeetResult -> meetWk_graph -> 'a1

  val meetWk_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakensTo -> meetWk_graph

  val meetWk_elim :
    'a1 -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> coq_WeakensTo ->
    'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    'a1 -> 'a1) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakensTo -> 'a1

  val coq_FunctionalElimination_meetWk :
    __ -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> coq_WeakensTo -> coq_WeakensTo ->
    __ -> __) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    __ -> __) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    __ -> __) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo -> coq_WeakensTo ->
    __ -> __) -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakensTo -> __

  val coq_FunctionalInduction_meetWk :
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    coq_WeakensTo -> coq_WeakensTo coq_MeetResult) functionalInduction

  val substUnivMeet_weaken : coq_WeakensTo coq_SubstUnivMeet

  val wkVar :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> coq_WeakensTo

  val coq_FunctionalInduction_transWk_assoc : __ functionalInduction

  val substUnivVar_weaken : coq_WeakensTo coq_SubstUnivVar

  val substUnivVarUp_weaken : coq_WeakensTo coq_SubstUnivVarUp

  val substUnivVarDown_weaken : coq_WeakensTo coq_SubstUnivVarDown

  val restrictEnv :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_WeakensTo ->
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding, 'a1) Coq_env.coq_Env ->
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding, 'a1) Coq_env.coq_Env

  val elimWeakenedVarZero :
    (coq_WeakensTo, 'a1) coq_SubstSU -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 -> 'a1) -> (coq_WeakensTo,
    'a1) coq_Weakened -> (coq_WeakensTo, 'a1) coq_Weakened

  val elimWeakenedVar :
    (coq_WeakensTo, 'a1) coq_SubstSU -> (coq_WeakensTo, 'a2) coq_SubstSU ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1 -> 'a2) -> (coq_WeakensTo, 'a1)
    coq_Weakened -> (coq_WeakensTo, 'a2) coq_Weakened

  val old_occurs_check :
    (coq_WeakensTo, 'a1) coq_SubstSU -> (coq_WeakensTo, 'a1)
    coq_GenOccursCheck -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1 -> 'a1 option

  type ('t, 'a) coq_Inst =
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 't ->
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val)
    Coq_env.coq_Env -> 'a

  val inst :
    ('a1, 'a2) coq_Inst -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding,
    Coq_ty.coq_Val) Coq_env.coq_Env -> 'a2

  type ('t, 'a) coq_Lift =
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a -> 't

  val lift :
    ('a1, 'a2) coq_Lift -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a2 -> 'a1

  val inst_list : ('a1, 'a2) coq_Inst -> ('a1 coq_List, 'a2 list) coq_Inst

  val lift_list : ('a1, 'a2) coq_Lift -> ('a1 coq_List, 'a2 list) coq_Lift

  val inst_const : ('a1 coq_Const, 'a1) coq_Inst

  val lift_const : ('a1 coq_Const, 'a1) coq_Lift

  val inst_env :
    ('a1 -> ('a2, 'a3) coq_Inst) -> 'a1 Coq_ctx.coq_Ctx -> (('a1, 'a2)
    Coq_env.coq_Env, ('a1, 'a3) Coq_env.coq_Env) coq_Inst

  val lift_env :
    ('a1 -> ('a2, 'a3) coq_Lift) -> 'a1 Coq_ctx.coq_Ctx -> (('a1, 'a2)
    Coq_env.coq_Env, ('a1, 'a3) Coq_env.coq_Env) coq_Lift

  val inst_term : Coq_ty.coq_Ty -> (coq_Term, Coq_ty.coq_Val) coq_Inst

  val lift_term : Coq_ty.coq_Ty -> (coq_Term, Coq_ty.coq_Val) coq_Lift

  val inst_sub :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_Sub,
    ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val)
    Coq_env.coq_Env) coq_Inst

  val inst_unit : (coq_Unit, unit0) coq_Inst

  val lift_unit : (coq_Unit, unit0) coq_Lift

  val inst_pair :
    ('a1, 'a3) coq_Inst -> ('a2, 'a4) coq_Inst -> (('a1, 'a2) coq_Pair, ('a3,
    'a4) prod) coq_Inst

  val lift_pair :
    ('a1, 'a3) coq_Lift -> ('a2, 'a4) coq_Lift -> (('a1, 'a2) coq_Pair, ('a3,
    'a4) prod) coq_Lift

  val inst_option :
    ('a1, 'a2) coq_Inst -> ('a1 coq_Option, 'a2 option) coq_Inst

  val lift_option :
    ('a1, 'a2) coq_Lift -> ('a1 coq_Option, 'a2 option) coq_Lift

  val inst_store :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_SStore,
    (pVar, Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv) coq_Inst

  val term_get_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> Coq_ty.coq_Val option

  val term_get_pair :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_Term -> (coq_Term, coq_Term) prod
    option

  val term_get_sum :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_Term -> (coq_Term, coq_Term) sum
    option

  val term_get_list :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> ((coq_Term, coq_Term) prod, unit0) sum option

  val term_get_union :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.unioni -> coq_Term -> (Coq_ty.unionk, coq_Term) sigT option

  val term_get_record :
    Coq_ty.recordi -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_Term -> (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Term)
    namedEnv option

  val term_get_tuple :
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term -> (Coq_ty.coq_Ty,
    coq_Term) Coq_env.coq_Env option

  module Entailment :
   sig
    module Coq_tactics :
     sig
     end
   end

  type ('t, 'tE) coq_Erase =
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 't -> 'tE

  val erase :
    ('a1, 'a2) coq_Erase -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> 'a1 -> 'a2

  val erase_Unit : (coq_Unit, unit0) coq_Erase

  val erase_Const : ('a1 coq_Const, 'a1) coq_Erase

  val erase_Ctx :
    ('a1, 'a2) coq_Erase -> ('a1 Coq_ctx.coq_Ctx, 'a2 list) coq_Erase

  val erase_List : ('a1, 'a2) coq_Erase -> ('a1 list, 'a2 list) coq_Erase

  val erase_Term : Coq_ty.coq_Ty -> (coq_Term, coq_ETerm) coq_Erase

  val coq_EraseSStore :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_SStore,
    (pVar, Coq_ty.coq_Ty, coq_ETerm) namedEnv) coq_Erase

  module Coq_amsg :
   sig
    type 'm coq_CloseMessage =
    | Coq_there of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding * 'm

    val coq_CloseMessage_rect :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ((lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> 'a1 -> 'a2) -> 'a1
      coq_CloseMessage -> 'a2

    val coq_CloseMessage_rec :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ((lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> 'a1 -> 'a2) -> 'a1
      coq_CloseMessage -> 'a2

    val subst_closemessage : 'a1 coq_Subst -> 'a1 coq_CloseMessage coq_Subst

    val substSU_closemessage :
      (coq_WeakensTo, 'a1) coq_SubstSU -> (coq_WeakensTo, 'a1
      coq_CloseMessage) coq_SubstSU

    val substlaws_closemessage :
      'a1 coq_Subst -> 'a1 coq_SubstLaws -> 'a1 coq_CloseMessage coq_SubstLaws

    val occurscheck_closemessage :
      'a1 coq_OccursCheck -> 'a1 coq_CloseMessage coq_OccursCheck

    val erase_closemessage :
      ('a1, 'a2) coq_Erase -> ('a1 coq_CloseMessage, 'a2) coq_Erase

    type coq_AMessage =
    | Coq_mk of __ coq_Subst * (coq_WeakensTo, __) coq_SubstSU
       * __ coq_SubstLaws * __ coq_OccursCheck * (__, __) coq_Erase * 
       __

    val coq_AMessage_rect :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (__ -> __
      coq_Subst -> (coq_WeakensTo, __) coq_SubstSU -> __ -> __ coq_SubstLaws
      -> __ coq_OccursCheck -> __ -> (__, __) coq_Erase -> __ -> 'a1) ->
      coq_AMessage -> 'a1

    val coq_AMessage_rec :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (__ -> __
      coq_Subst -> (coq_WeakensTo, __) coq_SubstSU -> __ -> __ coq_SubstLaws
      -> __ coq_OccursCheck -> __ -> (__, __) coq_Erase -> __ -> 'a1) ->
      coq_AMessage -> 'a1

    val empty :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_AMessage

    val closeAux :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_WeakensTo,
      'a1) coq_SubstSU -> 'a1 coq_Subst -> 'a1 coq_SubstLaws -> 'a1
      coq_OccursCheck -> ('a1, 'a2) coq_Erase -> 'a1 -> coq_AMessage

    val close :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_AMessage ->
      coq_AMessage

    val subst_amessage : coq_AMessage coq_Subst

    val substSU_amessage : (coq_WeakensTo, coq_AMessage) coq_SubstSU

    val substlaws_amessage : coq_AMessage coq_SubstLaws

    val occurscheck_amessage :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> coq_AMessage -> coq_AMessage
      option

    type coq_EAMessage =
    | MkEAMessage of __

    val coq_EAMessage_rect : (__ -> __ -> 'a1) -> coq_EAMessage -> 'a1

    val coq_EAMessage_rec : (__ -> __ -> 'a1) -> coq_EAMessage -> 'a1

    val erase_amessage : (coq_AMessage, coq_EAMessage) coq_Erase

    val boxMsg :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_AMessage ->
      coq_AMessage

    val genoccurscheck_amessage :
      (coq_WeakensTo, coq_AMessage) coq_GenOccursCheck
   end

  type coq_TermRing = { tmr_zero : Coq_ty.coq_Val; tmr_one : Coq_ty.coq_Val;
                        tmr_plus : Coq_bop.coq_BinOp;
                        tmr_times : Coq_bop.coq_BinOp;
                        tmr_minus : Coq_bop.coq_BinOp;
                        tmr_negate : Coq_uop.coq_UnOp;
                        tmr_of_Z : (z -> Coq_ty.coq_Val) }

  val tmr_zero :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> Coq_ty.coq_Val

  val tmr_one :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> Coq_ty.coq_Val

  val tmr_plus :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> Coq_bop.coq_BinOp

  val tmr_times :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> Coq_bop.coq_BinOp

  val tmr_minus :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> Coq_bop.coq_BinOp

  val tmr_negate :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> Coq_uop.coq_UnOp

  val tmr_of_Z :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> z -> Coq_ty.coq_Val

  val coq_TermRing_int :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_TermRing

  val coq_TermRing_bv :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_TermRing

  val evalPExprTm :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> coq_Term list -> z pExpr -> coq_Term

  type coq_RQuote = coq_Term list -> positive -> (z pExpr, coq_Term list) prod

  val coq_Term_Quote_def :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> coq_RQuote

  val coq_Term_Quote_unop :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> (z pExpr -> z pExpr) -> coq_RQuote -> coq_RQuote

  val coq_Term_Quote_bin :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> (z pExpr -> z pExpr -> z pExpr) ->
    coq_RQuote -> coq_RQuote -> coq_RQuote

  type coq_CanonTerm = __

  val peval_append :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> coq_Term -> coq_Term

  val peval_and_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term ->
    Coq_ty.coq_Val -> coq_Term

  val peval_or_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term ->
    Coq_ty.coq_Val -> coq_Term

  val peval_and :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term ->
    coq_Term -> coq_Term

  val peval_or :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term ->
    coq_Term -> coq_Term

  val peval_plus :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term ->
    coq_Term -> coq_Term

  type peval_plus_graph =
  | Coq_peval_plus_graph_equation_1 of lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_plus_graph_equation_2 of lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_plus_graph_equation_3 of lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In * positive
  | Coq_peval_plus_graph_equation_4 of lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In * positive
  | Coq_peval_plus_graph_equation_5 of lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_plus_graph_equation_6 of lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_plus_graph_equation_7 of lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_plus_graph_equation_8 of positive * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_plus_graph_equation_9 of positive * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_plus_graph_equation_10 of Coq_ty.coq_Val * Coq_ty.coq_Val
  | Coq_peval_plus_graph_equation_11 of Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_plus_graph_equation_12 of positive * Coq_ty.coq_Ty
     * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_plus_graph_equation_13 of positive * Coq_ty.coq_Ty
     * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_plus_graph_equation_14 of Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term
  | Coq_peval_plus_graph_equation_15 of positive * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_plus_graph_equation_16 of positive * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_plus_graph_equation_17 of Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_plus_graph_equation_18 of Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_plus_graph_equation_19 of Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term * positive
  | Coq_peval_plus_graph_equation_20 of Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term * positive
  | Coq_peval_plus_graph_equation_21 of Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term * Coq_ty.coq_Ty
     * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_plus_graph_equation_22 of Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_plus_graph_equation_23 of Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_plus_graph_equation_24 of Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term
  | Coq_peval_plus_graph_equation_25 of Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term * positive
  | Coq_peval_plus_graph_equation_26 of Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term * positive
  | Coq_peval_plus_graph_equation_27 of Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp
     * coq_Term * coq_Term
  | Coq_peval_plus_graph_equation_28 of Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term

  val peval_plus_graph_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    positive -> 'a1) -> (lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> positive -> 'a1) -> (lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (positive -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (positive ->
    lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1)
    -> (Coq_ty.coq_Val -> Coq_ty.coq_Val -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (positive -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> 'a1) -> (positive -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (positive ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (positive ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty
    -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp
    -> coq_Term -> coq_Term -> positive -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> positive ->
    'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term
    -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> positive -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> positive -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
    coq_Term -> 'a1) -> coq_Term -> coq_Term -> coq_Term -> peval_plus_graph
    -> 'a1

  val peval_plus_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term ->
    coq_Term -> peval_plus_graph

  val peval_plus_elim :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    positive -> 'a1) -> (lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> positive -> 'a1) -> (lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (positive -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (positive ->
    lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1)
    -> (Coq_ty.coq_Val -> Coq_ty.coq_Val -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (positive -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> 'a1) -> (positive -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (positive ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (positive ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty
    -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp
    -> coq_Term -> coq_Term -> positive -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> positive ->
    'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term
    -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> positive -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> positive -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
    coq_Term -> 'a1) -> coq_Term -> coq_Term -> 'a1

  val coq_FunctionalElimination_peval_plus :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) ->
    (lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    positive -> __) -> (lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> positive -> __) -> (lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __) -> (lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> (positive -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (positive ->
    lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __)
    -> (Coq_ty.coq_Val -> Coq_ty.coq_Val -> __) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) ->
    (positive -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> __) -> (positive -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) ->
    (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (positive ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (positive ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) ->
    (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> __) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp
    -> coq_Term -> coq_Term -> positive -> __) -> (Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> positive ->
    __) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term
    -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> __) -> (Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __) -> (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp
    -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> __) -> (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
    -> __) -> (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> positive ->
    __) -> (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> positive -> __)
    -> (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) ->
    (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __) -> coq_Term -> coq_Term -> __

  val coq_FunctionalInduction_peval_plus :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_Term ->
    coq_Term -> coq_Term) functionalInduction

  val peval_bvadd :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> coq_Term -> coq_Term

  type peval_bvadd_graph =
  | Coq_peval_bvadd_graph_equation_1 of nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvadd_graph_equation_2 of nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvadd_graph_equation_3 of nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In * positive
  | Coq_peval_bvadd_graph_equation_4 of nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvadd_graph_equation_5 of nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvadd_graph_equation_6 of nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvadd_graph_equation_7 of nat * positive * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvadd_graph_equation_8 of nat * Coq_ty.coq_Val * Coq_ty.coq_Val
  | Coq_peval_bvadd_graph_equation_9 of nat * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_bvadd_graph_equation_10 of nat * positive * Coq_ty.coq_Ty
     * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_bvadd_graph_equation_11 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvadd_graph_equation_12 of nat * positive * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvadd_graph_equation_13 of nat * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvadd_graph_equation_14 of nat * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_bvadd_graph_equation_15 of nat * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term * positive
  | Coq_peval_bvadd_graph_equation_16 of nat * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term * Coq_ty.coq_Ty
     * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_bvadd_graph_equation_17 of nat * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvadd_graph_equation_18 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvadd_graph_equation_19 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvadd_graph_equation_20 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * positive
  | Coq_peval_bvadd_graph_equation_21 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_bvadd_graph_equation_22 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term

  val peval_bvadd_graph_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat
    -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __
    -> 'a1) -> (nat -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> positive -> __ -> 'a1) -> (nat -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> __ ->
    lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1)
    -> (nat -> positive -> __ -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Val ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> __ -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> positive ->
    __ -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> __ -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
    coq_Term -> 'a1) -> (nat -> positive -> __ -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> __ -> 'a1) -> (nat -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> positive -> __ -> 'a1) ->
    (nat -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term
    -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __ -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> positive -> __ -> 'a1) -> (nat ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> nat -> coq_Term -> coq_Term ->
    coq_Term -> peval_bvadd_graph -> 'a1

  val peval_bvadd_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> coq_Term -> peval_bvadd_graph

  val peval_bvadd_elim :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat
    -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __
    -> 'a1) -> (nat -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> positive -> __ -> 'a1) -> (nat -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> __ ->
    lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1)
    -> (nat -> positive -> __ -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Val ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> __ -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> positive ->
    __ -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> __ -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
    coq_Term -> 'a1) -> (nat -> positive -> __ -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> __ -> 'a1) -> (nat -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> positive -> __ -> 'a1) ->
    (nat -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term
    -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __ -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> positive -> __ -> 'a1) -> (nat ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> nat -> coq_Term -> coq_Term -> 'a1

  val coq_FunctionalElimination_peval_bvadd :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat
    -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __
    -> __) -> (nat -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> positive -> __ -> __) -> (nat -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat
    -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> __ ->
    lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __)
    -> (nat -> positive -> __ -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> Coq_ty.coq_Val ->
    Coq_ty.coq_Val -> __) -> (nat -> __ -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> positive ->
    __ -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> __) -> (nat -> __ -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
    coq_Term -> __) -> (nat -> positive -> __ -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> __ -> __) -> (nat -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> positive -> __ -> __) ->
    (nat -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term
    -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __ -> __) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> positive -> __ -> __) -> (nat ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat
    -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __) -> nat -> coq_Term -> coq_Term -> __

  val coq_FunctionalInduction_peval_bvadd :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> coq_Term -> coq_Term) functionalInduction

  val peval_bvand_val_default :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term

  val peval_bvand_bvapp_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term) -> nat -> nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term

  val peval_bvand_bvcons_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term) -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> coq_Term

  val peval_bvand_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term

  type peval_bvand_val_graph =
  | Coq_peval_bvand_val_graph_equation_1 of nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_2 of nat * Coq_ty.coq_Val
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_3 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_4 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_5 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_6 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_7 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_8 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_9 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_10 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_11 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_12 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_13 of nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Val
  | Coq_peval_bvand_val_graph_equation_14 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * Coq_ty.coq_Val

  val peval_bvand_val_graph_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val
    -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat -> __ ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term -> peval_bvand_val_graph -> 'a1

  val peval_bvand_val_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> Coq_ty.coq_Val -> peval_bvand_val_graph

  val peval_bvand_val_elim :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val
    -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat -> __ ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> nat ->
    coq_Term -> Coq_ty.coq_Val -> 'a1

  val coq_FunctionalElimination_peval_bvand_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    Coq_ty.coq_Val -> __) -> (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val -> __)
    -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat
    -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> __) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val
    -> __) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat -> nat -> __ -> coq_Term
    -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> __) -> nat -> coq_Term
    -> Coq_ty.coq_Val -> __

  val coq_FunctionalInduction_peval_bvand_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term) functionalInduction

  val peval_bvand :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> coq_Term -> coq_Term

  type peval_bvand_graph =
  | Coq_peval_bvand_graph_equation_1 of nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In * coq_Term
  | Coq_peval_bvand_graph_equation_2 of nat * Coq_ty.coq_Val * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvand_graph_equation_3 of nat * Coq_ty.coq_Val * Coq_ty.coq_Val
  | Coq_peval_bvand_graph_equation_4 of nat * Coq_ty.coq_Val * nat * 
     coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_5 of nat * Coq_ty.coq_Val * nat * 
     coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_6 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvand_graph_equation_7 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvand_graph_equation_8 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvand_graph_equation_9 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvand_graph_equation_10 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvand_graph_equation_11 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvand_graph_equation_12 of nat * nat * Coq_ty.coq_Val
     * coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_13 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvand_graph_equation_14 of nat * Coq_ty.coq_Val * nat * 
     nat * coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_15 of nat * Coq_ty.coq_Val * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvand_graph_equation_16 of nat * nat * coq_Term * coq_Term
     * coq_Term
  | Coq_peval_bvand_graph_equation_17 of nat * nat * coq_Term * coq_Term
     * coq_Term
  | Coq_peval_bvand_graph_equation_18 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_19 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_20 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_21 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_22 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_23 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_24 of nat * nat * coq_Term * coq_Term
     * lVar * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvand_graph_equation_25 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_graph_equation_26 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvand_graph_equation_27 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvand_graph_equation_28 of nat * coq_Term * coq_Term * 
     lVar * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvand_graph_equation_29 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvand_graph_equation_30 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvand_graph_equation_31 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvand_graph_equation_32 of nat * nat * nat * coq_Term
     * coq_Term * coq_Term
  | Coq_peval_bvand_graph_equation_33 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * coq_Term

  val peval_bvand_graph_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_Term
    -> 'a1) -> (nat -> Coq_ty.coq_Val -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Val ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term -> coq_Term
    -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat
    -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term ->
    'a1) -> (nat -> nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    Coq_ty.coq_Val -> nat -> nat -> __ -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
    -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term
    -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1)
    -> (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat -> nat -> __ ->
    coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> coq_Term -> 'a1) -> nat -> coq_Term ->
    coq_Term -> coq_Term -> peval_bvand_graph -> 'a1

  val peval_bvand_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> coq_Term -> peval_bvand_graph

  val peval_bvand_elim :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_Term
    -> 'a1) -> (nat -> Coq_ty.coq_Val -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Val ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term -> coq_Term
    -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat
    -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term ->
    'a1) -> (nat -> nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    Coq_ty.coq_Val -> nat -> nat -> __ -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
    -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term
    -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1)
    -> (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat -> nat -> __ ->
    coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> coq_Term -> 'a1) -> nat -> coq_Term ->
    coq_Term -> 'a1

  val coq_FunctionalElimination_peval_bvand :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_Term
    -> __) -> (nat -> Coq_ty.coq_Val -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> Coq_ty.coq_Val ->
    Coq_ty.coq_Val -> __) -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term ->
    coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term -> coq_Term
    -> __) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat
    -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat ->
    Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val
    -> coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> coq_Term ->
    coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> __)
    -> (nat -> nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat
    -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat ->
    Coq_ty.coq_Val -> nat -> nat -> __ -> coq_Term -> coq_Term -> __) -> (nat
    -> Coq_ty.coq_Val -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __)
    -> (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat -> nat
    -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat -> coq_Term ->
    coq_Term -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term -> coq_Term
    -> __) -> (nat -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat ->
    coq_Term -> coq_Term -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term
    -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term -> coq_Term -> __) ->
    (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat -> coq_Term -> coq_Term
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> __) -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term ->
    lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __)
    -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat
    -> nat -> nat -> __ -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> coq_Term -> __) -> nat
    -> coq_Term -> coq_Term -> __

  val coq_FunctionalInduction_peval_bvand :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> coq_Term -> coq_Term) functionalInduction

  val peval_bvor_val_default :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term

  val peval_bvor_bvapp_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term) -> nat -> nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term

  val peval_bvor_bvcons_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term) -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> coq_Term

  val peval_bvor_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term

  type peval_bvor_val_graph =
  | Coq_peval_bvor_val_graph_equation_1 of nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_2 of nat * Coq_ty.coq_Val
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_3 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_4 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_5 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_6 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_7 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_8 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_9 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_10 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_11 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_12 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_13 of nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Val
  | Coq_peval_bvor_val_graph_equation_14 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * Coq_ty.coq_Val

  val peval_bvor_val_graph_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val
    -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat -> __ ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term -> peval_bvor_val_graph -> 'a1

  val peval_bvor_val_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> Coq_ty.coq_Val -> peval_bvor_val_graph

  val peval_bvor_val_elim :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val
    -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat -> __ ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> nat ->
    coq_Term -> Coq_ty.coq_Val -> 'a1

  val coq_FunctionalElimination_peval_bvor_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    Coq_ty.coq_Val -> __) -> (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Val -> __)
    -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat
    -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> __) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val
    -> __) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat -> nat -> __ -> coq_Term
    -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> __) -> nat -> coq_Term
    -> Coq_ty.coq_Val -> __

  val coq_FunctionalInduction_peval_bvor_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> Coq_ty.coq_Val -> coq_Term) functionalInduction

  val peval_bvor :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> coq_Term -> coq_Term

  type peval_bvor_graph =
  | Coq_peval_bvor_graph_equation_1 of nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In * coq_Term
  | Coq_peval_bvor_graph_equation_2 of nat * Coq_ty.coq_Val * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvor_graph_equation_3 of nat * Coq_ty.coq_Val * Coq_ty.coq_Val
  | Coq_peval_bvor_graph_equation_4 of nat * Coq_ty.coq_Val * nat * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_5 of nat * Coq_ty.coq_Val * nat * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_6 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_7 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_8 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_9 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_10 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_11 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_12 of nat * nat * Coq_ty.coq_Val * 
     coq_Term * coq_Term
  | Coq_peval_bvor_graph_equation_13 of nat * Coq_ty.coq_Val * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_14 of nat * Coq_ty.coq_Val * nat * 
     nat * coq_Term * coq_Term
  | Coq_peval_bvor_graph_equation_15 of nat * Coq_ty.coq_Val * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvor_graph_equation_16 of nat * nat * coq_Term * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_17 of nat * nat * coq_Term * coq_Term
     * coq_Term
  | Coq_peval_bvor_graph_equation_18 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvor_graph_equation_19 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvor_graph_equation_20 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvor_graph_equation_21 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvor_graph_equation_22 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvor_graph_equation_23 of nat * coq_Term * coq_Term * coq_Term
  | Coq_peval_bvor_graph_equation_24 of nat * nat * coq_Term * coq_Term
     * lVar * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvor_graph_equation_25 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_graph_equation_26 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvor_graph_equation_27 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvor_graph_equation_28 of nat * coq_Term * coq_Term * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvor_graph_equation_29 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvor_graph_equation_30 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvor_graph_equation_31 of nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvor_graph_equation_32 of nat * nat * nat * coq_Term * 
     coq_Term * coq_Term
  | Coq_peval_bvor_graph_equation_33 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * coq_Term

  val peval_bvor_graph_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_Term
    -> 'a1) -> (nat -> Coq_ty.coq_Val -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Val ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term -> coq_Term
    -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat
    -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term ->
    'a1) -> (nat -> nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    Coq_ty.coq_Val -> nat -> nat -> __ -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
    -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term
    -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1)
    -> (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat -> nat -> __ ->
    coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> coq_Term -> 'a1) -> nat -> coq_Term ->
    coq_Term -> coq_Term -> peval_bvor_graph -> 'a1

  val peval_bvor_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> coq_Term -> peval_bvor_graph

  val peval_bvor_elim :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_Term
    -> 'a1) -> (nat -> Coq_ty.coq_Val -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> Coq_ty.coq_Val ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term -> coq_Term
    -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat
    -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term ->
    'a1) -> (nat -> nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    Coq_ty.coq_Val -> nat -> nat -> __ -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> Coq_ty.coq_Val -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
    -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term
    -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1)
    -> (nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term
    -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat -> nat -> __ ->
    coq_Term -> coq_Term -> coq_Term -> 'a1) -> (nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> coq_Term -> 'a1) -> nat -> coq_Term ->
    coq_Term -> 'a1

  val coq_FunctionalElimination_peval_bvor :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> coq_Term
    -> __) -> (nat -> Coq_ty.coq_Val -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> Coq_ty.coq_Val ->
    Coq_ty.coq_Val -> __) -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term ->
    coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> nat -> coq_Term -> coq_Term
    -> __) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat
    -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat ->
    Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val
    -> coq_Term -> coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> coq_Term ->
    coq_Term -> __) -> (nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> __)
    -> (nat -> nat -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat
    -> Coq_ty.coq_Val -> coq_Term -> coq_Term -> __) -> (nat ->
    Coq_ty.coq_Val -> nat -> nat -> __ -> coq_Term -> coq_Term -> __) -> (nat
    -> Coq_ty.coq_Val -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __)
    -> (nat -> nat -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat -> nat
    -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat -> coq_Term ->
    coq_Term -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term -> coq_Term
    -> __) -> (nat -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat ->
    coq_Term -> coq_Term -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term
    -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term -> coq_Term -> __) ->
    (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat -> coq_Term -> coq_Term
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> __) -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term ->
    lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __)
    -> (nat -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat
    -> nat -> nat -> __ -> coq_Term -> coq_Term -> coq_Term -> __) -> (nat ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> coq_Term -> __) -> nat
    -> coq_Term -> coq_Term -> __

  val coq_FunctionalInduction_peval_bvor :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> coq_Term -> coq_Term) functionalInduction

  val peval_bvapp_val_r :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> coq_Term -> Coq_ty.coq_Val -> coq_Term

  val peval_bvapp :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> coq_Term -> coq_Term -> coq_Term

  type peval_bvapp_graph =
  | Coq_peval_bvapp_graph_equation_1 of nat * nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_2 of nat * nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_3 of nat * nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvapp_graph_equation_4 of nat * nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_5 of nat * nat * Coq_ty.coq_Val * 
     lVar * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_6 of nat * nat * Coq_ty.coq_Val
     * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_7 of nat * nat * Coq_ty.coq_Val
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvapp_graph_equation_8 of nat * nat * Coq_ty.coq_Val
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_9 of nat * nat * nat * coq_Term * 
     coq_Term * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_10 of nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_11 of nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp
     * coq_Term * coq_Term
  | Coq_peval_bvapp_graph_equation_12 of nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_13 of nat * nat * nat * coq_Term
     * coq_Term * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_14 of nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_15 of nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp
     * coq_Term * coq_Term
  | Coq_peval_bvapp_graph_equation_16 of nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_17 of nat * nat * coq_Term * coq_Term
     * lVar * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_18 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_19 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvapp_graph_equation_20 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_21 of nat * nat * coq_Term * coq_Term
     * lVar * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_22 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_23 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvapp_graph_equation_24 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_25 of nat * nat * coq_Term * coq_Term
     * lVar * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_26 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_27 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvapp_graph_equation_28 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_29 of nat * nat * coq_Term * coq_Term
     * lVar * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_30 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_31 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvapp_graph_equation_32 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_33 of nat * nat * coq_Term * coq_Term
     * lVar * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_34 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_35 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvapp_graph_equation_36 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_37 of nat * nat * coq_Term * coq_Term
     * lVar * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_38 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_39 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvapp_graph_equation_40 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_41 of nat * nat * nat * coq_Term
     * coq_Term * coq_Term
  | Coq_peval_bvapp_graph_equation_42 of nat * nat * coq_Term * coq_Term
     * lVar * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_43 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_44 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp * coq_Term * 
     coq_Term
  | Coq_peval_bvapp_graph_equation_45 of nat * nat * coq_Term * coq_Term
     * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_46 of nat * nat * nat * nat * coq_Term
     * coq_Term * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_47 of nat * nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_48 of nat * nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Ty * Coq_ty.coq_Ty * Coq_bop.coq_BinOp
     * coq_Term * coq_Term
  | Coq_peval_bvapp_graph_equation_49 of nat * nat * nat * nat * coq_Term
     * coq_Term * Coq_ty.coq_Ty * Coq_uop.coq_UnOp * coq_Term
  | Coq_peval_bvapp_graph_equation_50 of nat * nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_bvapp_graph_equation_51 of nat * nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * Coq_ty.coq_Val
  | Coq_peval_bvapp_graph_equation_52 of nat * nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * Coq_ty.coq_Ty * Coq_ty.coq_Ty
     * Coq_bop.coq_BinOp * coq_Term * coq_Term
  | Coq_peval_bvapp_graph_equation_53 of nat * nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term * Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term

  val peval_bvapp_graph_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> nat
    -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1)
    -> (nat -> nat -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1)
    -> (nat -> nat -> Coq_ty.coq_Val -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat ->
    Coq_ty.coq_Val -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> Coq_ty.coq_Val
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> Coq_ty.coq_Val -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat -> nat -> coq_Term ->
    coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat ->
    nat -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
    -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat -> nat -> nat ->
    __ -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> nat -> nat
    -> __ -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    nat -> nat -> __ -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> nat -> nat -> __ -> coq_Term -> coq_Term -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> 'a1)
    -> (nat -> nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
    coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> nat
    -> nat -> coq_Term -> coq_Term -> coq_Term -> peval_bvapp_graph -> 'a1

  val peval_bvapp_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> coq_Term -> coq_Term -> peval_bvapp_graph

  val peval_bvapp_elim :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> nat
    -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1)
    -> (nat -> nat -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1)
    -> (nat -> nat -> Coq_ty.coq_Val -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat ->
    Coq_ty.coq_Val -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> Coq_ty.coq_Val
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> Coq_ty.coq_Val -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat -> nat -> coq_Term ->
    coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat ->
    nat -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term
    -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    'a1) -> (nat -> nat -> nat -> coq_Term -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat -> nat -> nat ->
    __ -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat -> nat -> nat
    -> __ -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat ->
    nat -> nat -> __ -> coq_Term -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> nat -> nat -> nat -> __ -> coq_Term -> coq_Term -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> (nat -> nat -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> 'a1) -> (nat -> nat ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Val -> 'a1)
    -> (nat -> nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> 'a1) -> (nat -> nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
    coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> nat
    -> nat -> coq_Term -> coq_Term -> 'a1

  val coq_FunctionalElimination_peval_bvapp :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> nat
    -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __)
    -> (nat -> nat -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> Coq_ty.coq_Val -> __) -> (nat -> nat -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat
    -> nat -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) ->
    (nat -> nat -> Coq_ty.coq_Val -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat ->
    Coq_ty.coq_Val -> Coq_ty.coq_Val -> __) -> (nat -> nat -> Coq_ty.coq_Val
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> __) -> (nat -> nat -> Coq_ty.coq_Val -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> nat -> nat -> coq_Term ->
    coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> __) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Val -> __) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> __) -> (nat -> nat -> nat -> coq_Term -> coq_Term ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> nat ->
    nat -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    __) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    __) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    __) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    __) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    __) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    __) -> (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat
    -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
    coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term ->
    __) -> (nat -> nat -> nat -> coq_Term -> coq_Term -> coq_Term -> __) ->
    (nat -> nat -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat -> coq_Term ->
    coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat -> coq_Term -> coq_Term
    -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp -> coq_Term ->
    coq_Term -> __) -> (nat -> nat -> coq_Term -> coq_Term -> Coq_ty.coq_Ty
    -> Coq_uop.coq_UnOp -> coq_Term -> __) -> (nat -> nat -> nat -> nat -> __
    -> coq_Term -> coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> __) -> (nat -> nat -> nat -> nat ->
    __ -> coq_Term -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat -> nat
    -> nat -> __ -> coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat -> nat ->
    nat -> __ -> coq_Term -> coq_Term -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
    coq_Term -> __) -> (nat -> nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
    coq_Term -> lVar -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> __) -> (nat -> nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp
    -> coq_Term -> Coq_ty.coq_Val -> __) -> (nat -> nat -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
    Coq_bop.coq_BinOp -> coq_Term -> coq_Term -> __) -> (nat -> nat ->
    Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __) -> nat -> nat -> coq_Term -> coq_Term
    -> __

  val coq_FunctionalInduction_peval_bvapp :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> nat
    -> coq_Term -> coq_Term -> coq_Term) functionalInduction

  val peval_bvdrop_bvapp :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> nat
    -> nat -> coq_Term -> __ -> coq_Term) -> nat -> nat -> nat -> nat ->
    coq_Term -> coq_Term -> coq_Term

  val peval_bvdrop_bvcons :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> nat
    -> nat -> coq_Term -> __ -> coq_Term) -> nat -> nat -> nat -> coq_Term ->
    coq_Term -> coq_Term

  val peval_bvdrop_bvdrop :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> nat
    -> nat -> coq_Term -> __ -> coq_Term) -> nat -> nat -> nat -> nat ->
    coq_Term -> coq_Term

  val peval_bvdrop_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> nat -> Coq_ty.coq_Val -> coq_Term

  val peval_bvdrop_default :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> nat -> coq_Term -> coq_Term

  val peval_bvdrop_eq :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> nat -> coq_Term -> coq_Term

  val peval_bvdrop :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> coq_Term -> coq_Term

  val peval_bvtake_bvapp :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> nat
    -> nat -> coq_Term -> __ -> coq_Term) -> nat -> nat -> nat -> nat ->
    coq_Term -> coq_Term -> coq_Term

  val peval_bvtake_bvcons :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> nat
    -> nat -> coq_Term -> __ -> coq_Term) -> nat -> nat -> nat -> coq_Term ->
    coq_Term -> coq_Term

  val peval_bvtake_bvtake :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> nat
    -> nat -> coq_Term -> __ -> coq_Term) -> nat -> nat -> nat -> nat ->
    coq_Term -> coq_Term

  val peval_bvtake_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> nat -> Coq_ty.coq_Val -> coq_Term

  val peval_bvtake_default :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> nat -> coq_Term -> coq_Term

  val peval_bvtake_eq :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> nat -> coq_Term -> coq_Term

  val peval_bvtake :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> coq_Term -> coq_Term

  val peval_update_vector_subrange :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> nat -> coq_Term -> coq_Term -> coq_Term

  val peval_binop' :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> coq_Term

  val peval_binop :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_Term -> coq_Term -> coq_Term

  val peval_not :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term ->
    coq_Term

  type peval_not_graph =
  | Coq_peval_not_graph_equation_1 of lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_not_graph_equation_2 of Coq_ty.coq_Val
  | Coq_peval_not_graph_equation_3 of coq_Term * coq_Term * peval_not_graph
     * peval_not_graph
  | Coq_peval_not_graph_equation_4 of coq_Term * coq_Term * peval_not_graph
     * peval_not_graph
  | Coq_peval_not_graph_equation_5 of Coq_ty.coq_Ty * Coq_bop.coq_RelOp
     * coq_Term * coq_Term
  | Coq_peval_not_graph_equation_6 of Coq_ty.coq_Ty * Coq_uop.coq_UnOp
     * coq_Term

  val peval_not_graph_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (Coq_ty.coq_Val -> 'a1) -> (coq_Term -> coq_Term -> peval_not_graph ->
    'a1 -> peval_not_graph -> 'a1 -> 'a1) -> (coq_Term -> coq_Term ->
    peval_not_graph -> 'a1 -> peval_not_graph -> 'a1 -> 'a1) ->
    (Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> coq_Term -> coq_Term -> 'a1) ->
    (Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> coq_Term ->
    coq_Term -> peval_not_graph -> 'a1

  val peval_not_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Term ->
    peval_not_graph

  val peval_not_elim :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (Coq_ty.coq_Val -> 'a1) -> (coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) ->
    (coq_Term -> coq_Term -> 'a1 -> 'a1 -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_bop.coq_RelOp -> coq_Term -> coq_Term -> 'a1) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> 'a1) -> coq_Term -> 'a1

  val coq_FunctionalElimination_peval_not :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) ->
    (Coq_ty.coq_Val -> __) -> (coq_Term -> coq_Term -> __ -> __ -> __) ->
    (coq_Term -> coq_Term -> __ -> __ -> __) -> (Coq_ty.coq_Ty ->
    Coq_bop.coq_RelOp -> coq_Term -> coq_Term -> __) -> (Coq_ty.coq_Ty ->
    Coq_uop.coq_UnOp -> coq_Term -> __) -> coq_Term -> __

  val coq_FunctionalInduction_peval_not :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_Term ->
    coq_Term) functionalInduction

  val peval_unsigned_bvapp :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> coq_Term -> coq_Term -> coq_Term

  val peval_unsigned :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> coq_Term

  type peval_unsigned_graph =
  | Coq_peval_unsigned_graph_equation_1 of nat * lVar
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
  | Coq_peval_unsigned_graph_equation_2 of nat * Coq_ty.coq_Val
  | Coq_peval_unsigned_graph_equation_3 of nat * nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_4 of nat * nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_5 of nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_6 of nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_7 of nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_8 of nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_9 of nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_10 of nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_11 of nat * nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_12 of nat * coq_Term * coq_Term
  | Coq_peval_unsigned_graph_equation_13 of nat * nat * nat * coq_Term
     * coq_Term
  | Coq_peval_unsigned_graph_equation_14 of nat * Coq_ty.coq_Ty
     * Coq_uop.coq_UnOp * coq_Term

  val peval_unsigned_graph_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (nat -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term
    -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term
    -> coq_Term -> 'a1) -> (nat -> nat -> nat -> __ -> coq_Term -> coq_Term
    -> 'a1) -> (nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1)
    -> nat -> coq_Term -> coq_Term -> peval_unsigned_graph -> 'a1

  val peval_unsigned_graph_correct :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    coq_Term -> peval_unsigned_graph

  val peval_unsigned_elim :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> 'a1) ->
    (nat -> Coq_ty.coq_Val -> 'a1) -> (nat -> nat -> coq_Term -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term
    -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) -> (nat ->
    coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term -> 'a1) ->
    (nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term -> coq_Term ->
    'a1) -> (nat -> nat -> coq_Term -> coq_Term -> 'a1) -> (nat -> coq_Term
    -> coq_Term -> 'a1) -> (nat -> nat -> nat -> __ -> coq_Term -> coq_Term
    -> 'a1) -> (nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> 'a1)
    -> nat -> coq_Term -> 'a1

  val coq_FunctionalElimination_peval_unsigned :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat -> lVar
    -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> __) ->
    (nat -> Coq_ty.coq_Val -> __) -> (nat -> nat -> coq_Term -> coq_Term ->
    __) -> (nat -> nat -> coq_Term -> coq_Term -> __) -> (nat -> coq_Term ->
    coq_Term -> __) -> (nat -> coq_Term -> coq_Term -> __) -> (nat ->
    coq_Term -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term -> __) ->
    (nat -> coq_Term -> coq_Term -> __) -> (nat -> coq_Term -> coq_Term ->
    __) -> (nat -> nat -> coq_Term -> coq_Term -> __) -> (nat -> coq_Term ->
    coq_Term -> __) -> (nat -> nat -> nat -> __ -> coq_Term -> coq_Term ->
    __) -> (nat -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> __) ->
    nat -> coq_Term -> __

  val coq_FunctionalInduction_peval_unsigned :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (nat ->
    coq_Term -> coq_Term) functionalInduction

  val peval_vector_subrange :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> nat -> coq_Term -> coq_Term

  val peval_unop' :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> coq_Term

  val peval_zext :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat -> nat
    -> coq_Term -> coq_Term

  val peval_unop :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_Term -> coq_Term

  val evalPolTm :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_TermRing -> coq_Term list -> z pol -> coq_Term

  val coq_CanonTerm_to_Term :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_CanonTerm -> coq_Term

  val peval_union :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.unioni -> Coq_ty.unionk -> coq_Term -> coq_Term

  val peval_record' :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (Coq_ty.recordf, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Term) namedEnv -> (Coq_ty.recordf,
    Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv option

  val peval_record :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.recordi -> (Coq_ty.recordf, Coq_ty.coq_Ty, coq_Term) namedEnv ->
    coq_Term

  val coq_CanonTerm_def :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> coq_CanonTerm

  val peval2_val :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Val -> coq_CanonTerm

  val peval2_binop :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
    coq_CanonTerm -> coq_CanonTerm -> coq_CanonTerm

  val peval2_unop :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp -> coq_CanonTerm ->
    coq_CanonTerm

  val peval2 :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> coq_CanonTerm

  val peval :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Term -> coq_Term

  val pevals :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, coq_Term)
    Coq_env.coq_Env -> (Coq_ty.coq_Ty, coq_Term) Coq_env.coq_Env

  type 'n coq_SMatchResult =
    ('n coq_PatternCase, ('n, Coq_ty.coq_Ty, coq_Term) namedEnv) sigT

  val pattern_match_term_reverse :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> 'a1 coq_Pattern -> 'a1 coq_PatternCase -> ('a1,
    Coq_ty.coq_Ty, coq_Term) namedEnv -> coq_Term

  val seval_exp :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SStore ->
    Coq_ty.coq_Ty -> coq_Exp -> coq_Term

  val seval_exps :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SStore -> ('a1,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1,
    Coq_ty.coq_Ty, coq_Exp) namedEnv -> ('a1, Coq_ty.coq_Ty, coq_Term)
    namedEnv

  type 'p coq_Precise = { prec_input : Coq_ty.coq_Ty Coq_ctx.coq_Ctx;
                          prec_output : Coq_ty.coq_Ty Coq_ctx.coq_Ctx }

  val prec_input :
    ('a1 -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx) -> 'a1 -> 'a1 coq_Precise ->
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx

  val prec_output :
    ('a1 -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx) -> 'a1 -> 'a1 coq_Precise ->
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx
 end

type pmpEntryCfg = (pmpcfg_ent, xlenbits0) prod

type pmpAddrRange = (xlenbits0, xlenbits0) prod option

val pmp_addr_range : pmpcfg_ent -> xlenbits0 -> xlenbits0 -> pmpAddrRange

val pmp_match_addr : xlenbits0 -> xlenbits0 -> pmpAddrRange -> pmpAddrMatch

val pmp_match_entry :
  xlenbits0 -> xlenbits0 -> privilege -> pmpcfg_ent -> xlenbits0 -> xlenbits0
  -> pmpMatch

val decide_access_pmp_perm : accessType -> pmpCfgPerm -> bool

val pmp_get_RWX : pmpcfg_ent -> privilege -> pmpCfgPerm

val pmp_get_perms : pmpcfg_ent -> privilege -> pmpCfgPerm

val pmp_check_rec :
  xlenbits0 -> xlenbits0 -> xlenbits0 -> pmpEntryCfg list -> privilege ->
  accessType -> bool

val pmp_check_aux :
  xlenbits0 -> xlenbits0 -> xlenbits0 -> pmpEntryCfg list -> privilege ->
  accessType -> bool

module RiscvPmpProgram :
 sig
  val width_constraint : nat -> bool

  type coq_Fun =
  | Coq_rX
  | Coq_wX
  | Coq_bool_to_bits
  | Coq_shift_right_arith32
  | Coq_extend_value of nat
  | Coq_get_arch_pc
  | Coq_get_next_pc
  | Coq_set_next_pc
  | Coq_tick_pc
  | Coq_to_bits of nat
  | Coq_within_phys_mem
  | Coq_mem_read of nat
  | Coq_checked_mem_read of nat
  | Coq_checked_mem_write of nat
  | Coq_pmp_mem_read of nat
  | Coq_pmp_mem_write of nat
  | Coq_pmpLocked
  | Coq_pmpWriteCfgReg
  | Coq_pmpWriteCfg
  | Coq_pmpWriteAddr
  | Coq_pmpCheck of nat
  | Coq_pmpCheckPerms
  | Coq_pmpCheckRWX
  | Coq_pmpMatchEntry
  | Coq_pmpAddrRange
  | Coq_pmpMatchAddr
  | Coq_process_load of nat
  | Coq_mem_write_value of nat
  | Coq_main
  | Coq_init_model
  | Coq_loop
  | Coq_step
  | Coq_fetch
  | Coq_init_sys
  | Coq_init_pmp
  | Coq_exceptionType_to_bits
  | Coq_interruptType_to_bits
  | Minterrupts_to_bits
  | Minterrupts_from_bits
  | Coq_privLevel_to_bits
  | Coq_handle_mem_exception
  | Coq_exception_handler
  | Coq_exception_delegatee
  | Coq_trap_handler
  | Coq_prepare_trap_vector
  | Coq_tvec_addr
  | Coq_handle_illegal
  | Coq_check_CSR
  | Coq_is_CSR_defined
  | Coq_csrAccess
  | Coq_csrPriv
  | Coq_check_CSR_access
  | Coq_readCSR
  | Coq_writeCSR
  | Coq_dispatchInterrupt
  | Coq_handle_interrupt
  | Coq_and_Minterrupts
  | Coq_processPending
  | Coq_getPendingSet
  | Coq_findPendingInterrupt
  | Coq_execute
  | Coq_execute_RTYPE
  | Coq_execute_ITYPE
  | Coq_execute_SHIFTIOP
  | Coq_execute_UTYPE
  | Coq_execute_BTYPE
  | Coq_execute_RISCV_JAL
  | Coq_execute_RISCV_JALR
  | Coq_execute_LOAD
  | Coq_execute_STORE
  | Coq_execute_ECALL
  | Coq_execute_EBREAK
  | Coq_execute_MRET
  | Coq_execute_CSR
  | Coq_execute_MUL

  val coq_Fun_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> (nat -> __ -> 'a1) -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> (nat -> 'a1) -> 'a1 -> (nat -> __ -> 'a1) -> (nat -> __ -> 'a1) ->
    (nat -> __ -> 'a1) -> (nat -> __ -> 'a1) -> (nat -> __ -> 'a1) -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> (nat -> __ -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> (nat -> __ -> 'a1) -> (nat -> __ -> 'a1) -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> Coq_ty.coq_Ty -> coq_Fun -> 'a1

  val coq_Fun_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> (nat -> __ -> 'a1) -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> (nat -> 'a1) -> 'a1 -> (nat -> __ -> 'a1) -> (nat -> __ -> 'a1) ->
    (nat -> __ -> 'a1) -> (nat -> __ -> 'a1) -> (nat -> __ -> 'a1) -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> (nat -> __ -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> (nat -> __ -> 'a1) -> (nat -> __ -> 'a1) -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> Coq_ty.coq_Ty -> coq_Fun -> 'a1

  type coq_FunX =
  | Coq_read_ram of nat
  | Coq_write_ram of nat
  | Coq_mmio_read of nat
  | Coq_mmio_write of nat
  | Coq_within_mmio of nat
  | Coq_decode
  | Coq_externalWorldUpdates

  val coq_FunX_rect :
    (nat -> 'a1) -> (nat -> 'a1) -> (nat -> 'a1) -> (nat -> __ -> 'a1) ->
    (nat -> __ -> 'a1) -> 'a1 -> 'a1 -> (pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> coq_FunX -> 'a1

  val coq_FunX_rec :
    (nat -> 'a1) -> (nat -> 'a1) -> (nat -> 'a1) -> (nat -> __ -> 'a1) ->
    (nat -> __ -> 'a1) -> 'a1 -> 'a1 -> (pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> coq_FunX -> 'a1

  type coq_Lem =
  | Coq_open_gprs
  | Coq_close_gprs
  | Coq_open_pmp_entries
  | Coq_close_pmp_entries
  | Coq_extract_pmp_ptsto of nat
  | Coq_return_pmp_ptsto of nat
  | Coq_open_ptsto_instr
  | Coq_close_ptsto_instr
  | Coq_close_mmio_write of Coq_bv.bv * wordWidth

  val coq_Lem_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> (nat -> 'a1) -> (nat -> 'a1) -> 'a1 -> 'a1 ->
    (Coq_bv.bv -> wordWidth -> 'a1) -> (pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Lem -> 'a1

  val coq_Lem_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> (nat -> 'a1) -> (nat -> 'a1) -> 'a1 -> 'a1 ->
    (Coq_bv.bv -> wordWidth -> 'a1) -> (pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Lem -> 'a1

  type _UU1d46d_ = coq_Fun

  type _UU1d46d__UU1d47f_ = coq_FunX

  type _UU1d473_ = coq_Lem

  type coq_Stm =
  | Coq_stm_val of Coq_ty.coq_Val
  | Coq_stm_exp of RiscvPmpBase.coq_Exp
  | Coq_stm_let of pVar * Coq_ty.coq_Ty * coq_Stm * coq_Stm
  | Coq_stm_block of (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * (pVar, Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv * coq_Stm
  | Coq_stm_assign of pVar
     * (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In * coq_Stm
  | Coq_stm_call of (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
     * coq_Fun * (pVar, Coq_ty.coq_Ty, RiscvPmpBase.coq_Exp) namedEnv
  | Coq_stm_call_frame of (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
                          Coq_ctx.coq_Ctx
     * (pVar, Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv * coq_Stm
  | Coq_stm_foreign of (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
                       Coq_ctx.coq_Ctx
     * coq_FunX * (pVar, Coq_ty.coq_Ty, RiscvPmpBase.coq_Exp) namedEnv
  | Coq_stm_lemmak of (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
                      Coq_ctx.coq_Ctx
     * coq_Lem * (pVar, Coq_ty.coq_Ty, RiscvPmpBase.coq_Exp) namedEnv
     * coq_Stm
  | Coq_stm_seq of Coq_ty.coq_Ty * coq_Stm * coq_Stm
  | Coq_stm_assertk of RiscvPmpBase.coq_Exp * RiscvPmpBase.coq_Exp * coq_Stm
  | Coq_stm_fail of Coq_ty.coq_Val
  | Coq_stm_pattern_match of Coq_ty.coq_Ty * coq_Stm
     * pVar RiscvPmpBase.coq_Pattern
     * (pVar RiscvPmpBase.coq_PatternCase -> coq_Stm)
  | Coq_stm_read_register of RiscvPmpBase.coq_Reg
  | Coq_stm_write_register of RiscvPmpBase.coq_Reg * RiscvPmpBase.coq_Exp
  | Coq_stm_bind of Coq_ty.coq_Ty * coq_Stm * (Coq_ty.coq_Val -> coq_Stm)
  | Coq_stm_debugk of coq_Stm

  val coq_Stm_rect :
    ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Val -> 'a1) -> ((pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    RiscvPmpBase.coq_Exp -> 'a1) -> ((pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> pVar ->
    Coq_ty.coq_Ty -> coq_Stm -> 'a1 -> coq_Stm -> 'a1 -> 'a1) -> ((pVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
    Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv -> coq_Stm -> 'a1 -> 'a1) ->
    ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> pVar -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> coq_Stm -> 'a1 -> 'a1) -> ((pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> (pVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Fun -> (pVar,
    Coq_ty.coq_Ty, RiscvPmpBase.coq_Exp) namedEnv -> 'a1) -> ((pVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
    Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv -> coq_Stm -> 'a1 -> 'a1) ->
    ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_FunX -> (pVar, Coq_ty.coq_Ty,
    RiscvPmpBase.coq_Exp) namedEnv -> 'a1) -> ((pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> (pVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Lem -> (pVar,
    Coq_ty.coq_Ty, RiscvPmpBase.coq_Exp) namedEnv -> coq_Stm -> 'a1 -> 'a1)
    -> ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_Stm -> 'a1 -> coq_Stm -> 'a1 ->
    'a1) -> ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> RiscvPmpBase.coq_Exp -> RiscvPmpBase.coq_Exp -> coq_Stm
    -> 'a1 -> 'a1) -> ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> Coq_ty.coq_Val -> 'a1) -> ((pVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> coq_Stm -> 'a1 -> pVar RiscvPmpBase.coq_Pattern -> (pVar
    RiscvPmpBase.coq_PatternCase -> coq_Stm) -> (pVar
    RiscvPmpBase.coq_PatternCase -> 'a1) -> 'a1) -> ((pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    RiscvPmpBase.coq_Reg -> 'a1) -> ((pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    RiscvPmpBase.coq_Reg -> RiscvPmpBase.coq_Exp -> 'a1) -> ((pVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> coq_Stm -> 'a1 -> (Coq_ty.coq_Val -> coq_Stm) ->
    (Coq_ty.coq_Val -> 'a1) -> 'a1) -> ((pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> coq_Stm -> 'a1 ->
    'a1) -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Stm -> 'a1

  val coq_Stm_rec :
    ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Val -> 'a1) -> ((pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    RiscvPmpBase.coq_Exp -> 'a1) -> ((pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> pVar ->
    Coq_ty.coq_Ty -> coq_Stm -> 'a1 -> coq_Stm -> 'a1 -> 'a1) -> ((pVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
    Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv -> coq_Stm -> 'a1 -> 'a1) ->
    ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> pVar -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_In -> coq_Stm -> 'a1 -> 'a1) -> ((pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> (pVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Fun -> (pVar,
    Coq_ty.coq_Ty, RiscvPmpBase.coq_Exp) namedEnv -> 'a1) -> ((pVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
    Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv -> coq_Stm -> 'a1 -> 'a1) ->
    ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_FunX -> (pVar, Coq_ty.coq_Ty,
    RiscvPmpBase.coq_Exp) namedEnv -> 'a1) -> ((pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> (pVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Lem -> (pVar,
    Coq_ty.coq_Ty, RiscvPmpBase.coq_Exp) namedEnv -> coq_Stm -> 'a1 -> 'a1)
    -> ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_Stm -> 'a1 -> coq_Stm -> 'a1 ->
    'a1) -> ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> RiscvPmpBase.coq_Exp -> RiscvPmpBase.coq_Exp -> coq_Stm
    -> 'a1 -> 'a1) -> ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> Coq_ty.coq_Val -> 'a1) -> ((pVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> coq_Stm -> 'a1 -> pVar RiscvPmpBase.coq_Pattern -> (pVar
    RiscvPmpBase.coq_PatternCase -> coq_Stm) -> (pVar
    RiscvPmpBase.coq_PatternCase -> 'a1) -> 'a1) -> ((pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    RiscvPmpBase.coq_Reg -> 'a1) -> ((pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    RiscvPmpBase.coq_Reg -> RiscvPmpBase.coq_Exp -> 'a1) -> ((pVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
    Coq_ty.coq_Ty -> coq_Stm -> 'a1 -> (Coq_ty.coq_Val -> coq_Stm) ->
    (Coq_ty.coq_Val -> 'a1) -> 'a1) -> ((pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> coq_Stm -> 'a1 ->
    'a1) -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Stm -> 'a1

  val coq_NoConfusionHomPackage_Stm :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Stm noConfusionPackage

  type coq_Stm_sig = coq_Stm

  val coq_Stm_sig_pack :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Stm -> ((pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx * Coq_ty.coq_Ty) * coq_Stm

  val coq_Stm_Signature :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> (coq_Stm, (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx * Coq_ty.coq_Ty, coq_Stm_sig) signature

  val stm_assert :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_Exp -> RiscvPmpBase.coq_Exp -> coq_Stm

  val stm_lemma :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Lem -> (pVar,
    Coq_ty.coq_Ty, RiscvPmpBase.coq_Exp) namedEnv -> coq_Stm

  val stm_if :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Stm -> coq_Stm -> coq_Stm -> coq_Stm

  val stm_match_prod :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_Stm -> pVar ->
    pVar -> coq_Stm -> coq_Stm

  val stm_match_tuple :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Stm -> pVar
    RiscvPmpBase.coq_TuplePat -> coq_Stm -> coq_Stm

  val stm_match_record :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.recordi -> (pVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Stm -> pVar
    RiscvPmpBase.coq_RecordPat -> coq_Stm -> coq_Stm

  val stm_match_bvec_split :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> nat -> nat -> coq_Stm -> pVar -> pVar -> coq_Stm ->
    coq_Stm

  val stm_match_list :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_Stm -> coq_Stm -> pVar -> pVar ->
    coq_Stm -> coq_Stm

  val stm_match_sum :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> coq_Stm -> pVar ->
    coq_Stm -> pVar -> coq_Stm -> coq_Stm

  val stm_match_enum :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.enumi -> coq_Stm -> (Coq_ty.enumt -> coq_Stm) ->
    coq_Stm

  val stm_match_bvec :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> nat -> coq_Stm -> (Coq_bv.bv -> coq_Stm) -> coq_Stm

  val stm_match_union_alt :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.unioni -> coq_Stm -> (Coq_ty.unionk -> (pVar,
    coq_Stm) RiscvPmpBase.coq_Alternative) -> coq_Stm

  type coq_UnionAlt = (pVar, coq_Stm) RiscvPmpBase.coq_Alternative

  type coq_UnionAlts = (Coq_ty.unionk, coq_UnionAlt) sigT list

  val findUnionAlt :
    Coq_ty.unioni -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> Coq_ty.unionk -> coq_UnionAlts ->
    coq_UnionAlt option

  val stm_match_union_alt_list :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.unioni -> coq_Stm -> coq_UnionAlts -> coq_Stm

  val stm_bindfree :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Stm -> bool

  val exp_smart_var :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> pVar ->
    Coq_ty.coq_Ty isSome -> RiscvPmpBase.coq_Exp

  val stm_smart_assign :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> pVar ->
    Coq_ty.coq_Ty isSome -> coq_Stm -> coq_Stm

  module Riscv_UU03bc_SailNotations :
   sig
   end

  val zero_reg :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Stm

  val stm_mstatus_from_bits :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Stm ->
    coq_Stm

  val stm_mstatus_to_bits :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Stm ->
    coq_Stm

  val fun_Minterrupts_to_bits : coq_Stm

  val exp_testbit :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
    RiscvPmpBase.coq_Exp -> n -> RiscvPmpBase.coq_Exp

  val stm_pmpcfg_ent_from_bits :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Stm ->
    coq_Stm

  val fun_Minterrupts_from_bits : coq_Stm

  val stm_pmpcfg_ent_to_bits :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Stm ->
    coq_Stm

  val fun_rX : coq_Stm

  val fun_wX : coq_Stm

  val fun_bool_to_bits : coq_Stm

  val fun_shift_right_arith32 : coq_Stm

  val fun_extend_value : nat -> coq_Stm

  val fun_get_arch_pc : coq_Stm

  val fun_get_next_pc : coq_Stm

  val fun_set_next_pc : coq_Stm

  val fun_tick_pc : coq_Stm

  val fun_to_bits : nat -> coq_Stm

  val fun_abs : coq_Stm

  val fun_within_phys_mem : coq_Stm

  val fun_mem_read : nat -> coq_Stm

  val fun_checked_mem_read : nat -> coq_Stm

  val fun_checked_mem_write : nat -> coq_Stm

  val fun_pmp_mem_read : nat -> coq_Stm

  val fun_pmp_mem_write : nat -> coq_Stm

  val fun_pmpLocked : coq_Stm

  val fun_pmpWriteCfgReg : coq_Stm

  val fun_pmpWriteCfg : coq_Stm

  val fun_pmpWriteAddr : coq_Stm

  val fun_pmpCheck : nat -> coq_Stm

  val fun_pmpCheckPerms : coq_Stm

  val fun_pmpCheckRWX : coq_Stm

  val fun_pmpMatchEntry : coq_Stm

  val fun_pmpAddrRange : coq_Stm

  val fun_pmpMatchAddr : coq_Stm

  val fun_process_load : nat -> coq_Stm

  val fun_mem_write_value : nat -> coq_Stm

  val fun_main : coq_Stm

  val fun_init_model : coq_Stm

  val fun_loop : coq_Stm

  val fun_fetch : coq_Stm

  val fun_step : coq_Stm

  val fun_init_sys : coq_Stm

  val fun_init_pmp : coq_Stm

  val fun_exceptionType_to_bits : coq_Stm

  val fun_interruptType_to_bits : coq_Stm

  val fun_handle_mem_exception : coq_Stm

  val fun_exception_handler : coq_Stm

  val fun_exception_delegatee : coq_Stm

  val fun_trap_handler : coq_Stm

  val fun_prepare_trap_vector : coq_Stm

  val fun_tvec_addr : coq_Stm

  val fun_handle_illegal : coq_Stm

  val fun_check_CSR : coq_Stm

  val fun_is_CSR_defined : coq_Stm

  val fun_csrAccess : coq_Stm

  val fun_csrPriv : coq_Stm

  val fun_check_CSR_access : coq_Stm

  val fun_privLevel_to_bits : coq_Stm

  val fun_readCSR : coq_Stm

  val fun_writeCSR : coq_Stm

  val fun_and_Minterrupts : coq_Stm

  val coq_Minterrupts_zero : minterrupts

  val fun_processPending : coq_Stm

  val fun_findPendingInterrupt : coq_Stm

  val fun_getPendingSet : coq_Stm

  val fun_dispatchInterrupt : coq_Stm

  val fun_handle_interrupt : coq_Stm

  val fun_execute : coq_Stm

  val fun_execute_MUL : coq_Stm

  val fun_execute_RTYPE : coq_Stm

  val fun_execute_ITYPE : coq_Stm

  val fun_execute_SHIFTIOP : coq_Stm

  val fun_execute_UTYPE : coq_Stm

  val fun_execute_RISCV_JAL : coq_Stm

  val fun_execute_RISCV_JALR : coq_Stm

  val fun_execute_BTYPE : coq_Stm

  val fun_execute_LOAD : coq_Stm

  val fun_execute_STORE : coq_Stm

  val fun_execute_ECALL : coq_Stm

  val fun_execute_EBREAK : coq_Stm

  val fun_execute_MRET : coq_Stm

  val fun_execute_CSR : coq_Stm

  type coq_RegStore = Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg -> Coq_ty.coq_Val

  val write_register :
    coq_RegStore -> Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg -> Coq_ty.coq_Val
    -> coq_RegStore

  val read_register :
    coq_RegStore -> Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg -> Coq_ty.coq_Val

  val coq_FunDef :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_Fun -> coq_Stm

  module Coq_callgraph :
   sig
    type coq_Node = { _UU0394_ : (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
                                 Coq_ctx.coq_Ctx;
                      _UU03c4_ : Coq_ty.coq_Ty; f : coq_Fun }

    val _UU0394_ :
      coq_Node -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

    val _UU03c4_ : coq_Node -> Coq_ty.coq_Ty

    val f : coq_Node -> coq_Fun

    type coq_CallGraph = coq_Node -> coq_Node list

    val coq_InvokedByStmList :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_Stm -> coq_Node list
   end

  val generic_call_graph : Coq_callgraph.coq_CallGraph

  module AccessibleTactics :
   sig
   end

  val _UU1d46d__call_graph : Coq_callgraph.coq_CallGraph

  module WithAccessibleTactics :
   sig
   end

  val _UU1d46d__accessible :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> _UU1d46d_ -> __ option
 end

type purePredicate =
| Gen_pmp_access
| Pmp_access
| Pmp_check_perms
| Pmp_check_rwx
| Sub_perm
| Access_pmp_perm
| Within_cfg
| Not_within_cfg
| Prev_addr
| In_entries
| In_mmio of nat

type exec =
| Left0
| Right0

type predicate =
| Pmp_entries
| Pmp_addr_access
| Pmp_addr_access_without of nat
| Gprs
| Ptsto
| Ptsto_one of exec
| Ptstomem_readonly of nat
| Inv_mmio of nat
| Mmio_checked_write of nat
| Encodes_instr
| Ptstomem of nat
| Ptstoinstr

val purePredicate_eqdec :
  purePredicate -> purePredicate -> purePredicate dec_eq

val exec_eqdec : exec -> exec -> exec dec_eq

val exec_EqDec : exec eqDec

val predicate_eqdec : predicate -> predicate -> predicate dec_eq

module RiscvPmpSignature :
 sig
  type _UU1d477_ = purePredicate

  val _UU1d477__Ty : _UU1d477_ -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx

  val default_pmpcfg_ent : pmpcfg_ent

  val default_pmpentries : (pmpcfg_ent, xlenbits0) prod list

  val pmp_check_RWX : Coq_ty.coq_Val -> Coq_ty.coq_Val -> bool

  val decide_pmp_check_perms :
    Coq_ty.coq_Val -> Coq_ty.coq_Val -> Coq_ty.coq_Val -> bool

  val access_type_eqb : Coq_ty.coq_Val -> Coq_ty.coq_Val -> bool

  val decide_sub_perm : Coq_ty.coq_Val -> Coq_ty.coq_Val -> bool

  val coq_PmpAddrMatchType_eqb : pmpAddrMatchType -> pmpAddrMatchType -> bool

  type coq_PmpAddrMatchType_eqb_graph =
  | PmpAddrMatchType_eqb_graph_equation_1
  | PmpAddrMatchType_eqb_graph_equation_2
  | PmpAddrMatchType_eqb_graph_equation_3
  | PmpAddrMatchType_eqb_graph_equation_4

  val coq_PmpAddrMatchType_eqb_graph_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> pmpAddrMatchType -> pmpAddrMatchType -> bool
    -> coq_PmpAddrMatchType_eqb_graph -> 'a1

  val coq_PmpAddrMatchType_eqb_graph_correct :
    pmpAddrMatchType -> pmpAddrMatchType -> coq_PmpAddrMatchType_eqb_graph

  val coq_PmpAddrMatchType_eqb_elim :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> pmpAddrMatchType -> pmpAddrMatchType -> 'a1

  val coq_FunctionalElimination_PmpAddrMatchType_eqb :
    __ -> __ -> __ -> __ -> pmpAddrMatchType -> pmpAddrMatchType -> __

  val coq_FunctionalInduction_PmpAddrMatchType_eqb :
    (pmpAddrMatchType -> pmpAddrMatchType -> bool) functionalInduction

  val pmpcfg_ent_eqb : pmpcfg_ent -> pmpcfg_ent -> bool

  val decide_in_entries :
    Coq_ty.coq_Val -> Coq_ty.coq_Val -> Coq_ty.coq_Val -> bool

  val decide_prev_addr :
    Coq_ty.coq_Val -> Coq_ty.coq_Val -> Coq_ty.coq_Val -> bool

  val decide_within_cfg :
    Coq_ty.coq_Val -> Coq_ty.coq_Val -> Coq_ty.coq_Val -> Coq_ty.coq_Val ->
    bool

  val decide_not_within_cfg : Coq_ty.coq_Val -> Coq_ty.coq_Val -> bool

  val is_pmp_cfg_unlocked : Coq_ty.coq_Val -> bool

  val _UU1d477__inst :
    _UU1d477_ -> (Coq_ty.coq_Ty, Coq_ty.coq_Val, __) Coq_env.abstract

  val _UU1d477__eq_dec : _UU1d477_ eqDec

  type _UU1d46f_ = predicate

  val _UU1d46f__Ty : _UU1d46f_ -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx

  val _UU1d46f__is_dup : predicate isDuplicable

  val _UU1d46f__eq_dec : _UU1d46f_ eqDec

  val _UU1d46f__precise :
    _UU1d46f_ -> _UU1d46f_ RiscvPmpBase.coq_Precise option

  type coq_PredicateDef = { lptsreg : (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg
                                      -> Coq_ty.coq_Val -> __);
                            luser : (predicate -> (Coq_ty.coq_Ty,
                                    Coq_ty.coq_Val) Coq_env.coq_Env -> __) }

  val lptsreg :
    bi -> coq_PredicateDef -> Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg ->
    Coq_ty.coq_Val -> __

  val luser :
    bi -> coq_PredicateDef -> predicate -> (Coq_ty.coq_Ty, Coq_ty.coq_Val)
    Coq_env.coq_Env -> __

  type coq_Formula =
  | Coq_formula_user of purePredicate
     * (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) Coq_env.coq_Env
  | Coq_formula_bool of RiscvPmpBase.coq_Term
  | Coq_formula_prop of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
                        Coq_ctx.coq_Ctx
     * RiscvPmpBase.coq_Sub
     * (lVar, Coq_ty.coq_Ty, Coq_ty.coq_Val, __) abstract_named
  | Coq_formula_relop of Coq_ty.coq_Ty * Coq_bop.coq_RelOp
     * RiscvPmpBase.coq_Term * RiscvPmpBase.coq_Term
  | Coq_formula_true
  | Coq_formula_false
  | Coq_formula_and of coq_Formula * coq_Formula
  | Coq_formula_or of coq_Formula * coq_Formula

  val coq_Formula_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (purePredicate -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) Coq_env.coq_Env
    -> 'a1) -> (RiscvPmpBase.coq_Term -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> RiscvPmpBase.coq_Sub -> (lVar,
    Coq_ty.coq_Ty, Coq_ty.coq_Val, __) abstract_named -> 'a1) ->
    (Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> RiscvPmpBase.coq_Term ->
    RiscvPmpBase.coq_Term -> 'a1) -> 'a1 -> 'a1 -> (coq_Formula -> 'a1 ->
    coq_Formula -> 'a1 -> 'a1) -> (coq_Formula -> 'a1 -> coq_Formula -> 'a1
    -> 'a1) -> coq_Formula -> 'a1

  val coq_Formula_rec :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (purePredicate -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) Coq_env.coq_Env
    -> 'a1) -> (RiscvPmpBase.coq_Term -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> RiscvPmpBase.coq_Sub -> (lVar,
    Coq_ty.coq_Ty, Coq_ty.coq_Val, __) abstract_named -> 'a1) ->
    (Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> RiscvPmpBase.coq_Term ->
    RiscvPmpBase.coq_Term -> 'a1) -> 'a1 -> 'a1 -> (coq_Formula -> 'a1 ->
    coq_Formula -> 'a1 -> 'a1) -> (coq_Formula -> 'a1 -> coq_Formula -> 'a1
    -> 'a1) -> coq_Formula -> 'a1

  val formula_relop_neg :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> RiscvPmpBase.coq_Term ->
    RiscvPmpBase.coq_Term -> coq_Formula

  val subSU_formula :
    'a1 RiscvPmpBase.coq_SubstUniv -> ('a1, coq_Formula)
    RiscvPmpBase.coq_SubstSU

  val sub_formula : coq_Formula RiscvPmpBase.coq_Subst

  val substlaws_formula : coq_Formula RiscvPmpBase.coq_SubstLaws

  val coq_OccursCheckFormula : coq_Formula RiscvPmpBase.coq_OccursCheck

  val coq_GenOccursCheckFormula :
    'a1 RiscvPmpBase.coq_SubstUniv -> 'a1 RiscvPmpBase.coq_SubstUnivMeet ->
    'a1 RiscvPmpBase.coq_SubstUnivVar -> 'a1 RiscvPmpBase.coq_SubstUniv ->
    'a1 RiscvPmpBase.coq_SubstUnivMeet -> 'a1 RiscvPmpBase.coq_SubstUniv ->
    'a1 RiscvPmpBase.coq_SubstUnivMeet -> ('a1, coq_Formula)
    RiscvPmpBase.coq_GenOccursCheck

  type coq_PathCondition = coq_Formula Coq_ctx.coq_Ctx

  val formula_eqs_ctx :
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty,
    RiscvPmpBase.coq_Term) Coq_env.coq_Env -> (Coq_ty.coq_Ty,
    RiscvPmpBase.coq_Term) Coq_env.coq_Env -> coq_PathCondition

  val formula_eqs_nctx :
    ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1,
    Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) namedEnv -> ('a1, Coq_ty.coq_Ty,
    RiscvPmpBase.coq_Term) namedEnv -> coq_PathCondition

  type coq_EFormula =
  | Coq_eformula_user of purePredicate
     * (Coq_ty.coq_Ty, RiscvPmpBase.coq_ETerm) Coq_env.coq_Env
  | Coq_eformula_bool of RiscvPmpBase.coq_ETerm
  | Coq_eformula_prop of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
                         Coq_ctx.coq_Ctx
     * ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding, RiscvPmpBase.coq_ETerm)
       Coq_env.coq_Env
     * (lVar, Coq_ty.coq_Ty, Coq_ty.coq_Val, __) abstract_named
  | Coq_eformula_relop of Coq_ty.coq_Ty * Coq_bop.coq_RelOp
     * RiscvPmpBase.coq_ETerm * RiscvPmpBase.coq_ETerm
  | Coq_eformula_true
  | Coq_eformula_false
  | Coq_eformula_and of coq_EFormula * coq_EFormula
  | Coq_eformula_or of coq_EFormula * coq_EFormula

  val coq_EFormula_rect :
    (purePredicate -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_ETerm) Coq_env.coq_Env
    -> 'a1) -> (RiscvPmpBase.coq_ETerm -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding, RiscvPmpBase.coq_ETerm) Coq_env.coq_Env -> (lVar,
    Coq_ty.coq_Ty, Coq_ty.coq_Val, __) abstract_named -> 'a1) ->
    (Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> RiscvPmpBase.coq_ETerm ->
    RiscvPmpBase.coq_ETerm -> 'a1) -> 'a1 -> 'a1 -> (coq_EFormula -> 'a1 ->
    coq_EFormula -> 'a1 -> 'a1) -> (coq_EFormula -> 'a1 -> coq_EFormula ->
    'a1 -> 'a1) -> coq_EFormula -> 'a1

  val coq_EFormula_rec :
    (purePredicate -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_ETerm) Coq_env.coq_Env
    -> 'a1) -> (RiscvPmpBase.coq_ETerm -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding, RiscvPmpBase.coq_ETerm) Coq_env.coq_Env -> (lVar,
    Coq_ty.coq_Ty, Coq_ty.coq_Val, __) abstract_named -> 'a1) ->
    (Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> RiscvPmpBase.coq_ETerm ->
    RiscvPmpBase.coq_ETerm -> 'a1) -> 'a1 -> 'a1 -> (coq_EFormula -> 'a1 ->
    coq_EFormula -> 'a1 -> 'a1) -> (coq_EFormula -> 'a1 -> coq_EFormula ->
    'a1 -> 'a1) -> coq_EFormula -> 'a1

  val erase_formula :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Formula
    -> coq_EFormula

  val erase_Formula : (coq_Formula, coq_EFormula) RiscvPmpBase.coq_Erase

  type 'v coq_GChunk =
  | Coq_chunk_user of predicate * (Coq_ty.coq_Ty, 'v) Coq_env.coq_Env
  | Coq_chunk_ptsreg of Coq_ty.coq_Ty * RiscvPmpBase.coq_Reg * 'v
  | Coq_chunk_conj of 'v coq_GChunk * 'v coq_GChunk
  | Coq_chunk_wand of 'v coq_GChunk * 'v coq_GChunk

  val coq_GChunk_rect :
    (predicate -> (Coq_ty.coq_Ty, 'a1) Coq_env.coq_Env -> 'a2) ->
    (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg -> 'a1 -> 'a2) -> ('a1 coq_GChunk
    -> 'a2 -> 'a1 coq_GChunk -> 'a2 -> 'a2) -> ('a1 coq_GChunk -> 'a2 -> 'a1
    coq_GChunk -> 'a2 -> 'a2) -> 'a1 coq_GChunk -> 'a2

  val coq_GChunk_rec :
    (predicate -> (Coq_ty.coq_Ty, 'a1) Coq_env.coq_Env -> 'a2) ->
    (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg -> 'a1 -> 'a2) -> ('a1 coq_GChunk
    -> 'a2 -> 'a1 coq_GChunk -> 'a2 -> 'a2) -> ('a1 coq_GChunk -> 'a2 -> 'a1
    coq_GChunk -> 'a2 -> 'a2) -> 'a1 coq_GChunk -> 'a2

  type coq_SCChunk = Coq_ty.coq_Val coq_GChunk

  type coq_Chunk = RiscvPmpBase.coq_Term coq_GChunk

  val coq_NoConfusionPackage_GChunk : 'a1 coq_GChunk noConfusionPackage

  val chunk_isdup : 'a1 coq_GChunk isDuplicable

  val chunk_eqb :
    (Coq_ty.coq_Ty -> 'a1 -> 'a1 -> bool) -> 'a1 coq_GChunk -> 'a1 coq_GChunk
    -> bool

  val chunk_eqb_spec :
    (Coq_ty.coq_Ty -> 'a1 -> 'a1 -> bool) -> (Coq_ty.coq_Ty -> 'a1 -> 'a1 ->
    reflect) -> 'a1 coq_GChunk -> 'a1 coq_GChunk -> reflect

  val coq_SubstChunk : coq_Chunk RiscvPmpBase.coq_Subst

  val coq_SubstSUChunk :
    'a1 RiscvPmpBase.coq_SubstUniv -> ('a1, coq_Chunk)
    RiscvPmpBase.coq_SubstSU

  val substlaws_chunk : coq_Chunk RiscvPmpBase.coq_SubstLaws

  val map_GChunk :
    (Coq_ty.coq_Ty -> 'a1 -> 'a2) -> 'a1 coq_GChunk -> 'a2 coq_GChunk

  val inst_chunk : (coq_Chunk, coq_SCChunk) RiscvPmpBase.coq_Inst

  val coq_OccursCheckChunk : coq_Chunk RiscvPmpBase.coq_OccursCheck

  val coq_GenOccursCheckChunk :
    (RiscvPmpBase.coq_WeakensTo, coq_Chunk) RiscvPmpBase.coq_GenOccursCheck

  type coq_SCHeap = coq_SCChunk list

  type coq_SHeap = coq_Chunk list

  val inst_heap : (coq_SHeap, coq_SCHeap) RiscvPmpBase.coq_Inst

  val peval_chunk :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Chunk ->
    coq_Chunk

  val try_consume_chunk_exact :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SHeap ->
    coq_Chunk -> coq_SHeap option

  val match_chunk_user_precise_clause_1 :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> predicate ->
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx ->
    (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) Coq_env.coq_Env -> (Coq_ty.coq_Ty,
    RiscvPmpBase.coq_Term) Coq_env.coq_Env -> predicate -> sumbool ->
    (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) Coq_env.coq_Env ->
    coq_PathCondition option

  val match_chunk_user_precise :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> predicate ->
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx ->
    (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) Coq_env.coq_Env -> (Coq_ty.coq_Ty,
    RiscvPmpBase.coq_Term) Coq_env.coq_Env -> coq_Chunk -> coq_PathCondition
    option

  val try_consume_chunk_user_precise :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> predicate ->
    Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx ->
    (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) Coq_env.coq_Env -> (Coq_ty.coq_Ty,
    RiscvPmpBase.coq_Term) Coq_env.coq_Env -> coq_SHeap -> (coq_SHeap,
    coq_PathCondition) prod option

  val match_chunk_ptsreg_precise_clause_1 :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg -> Coq_ty.coq_Ty ->
    RiscvPmpBase.coq_Reg -> sumbool -> RiscvPmpBase.coq_Term ->
    RiscvPmpBase.coq_Term option

  val match_chunk_ptsreg_precise :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg -> coq_Chunk ->
    RiscvPmpBase.coq_Term option

  val find_chunk_ptsreg_precise :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg -> coq_SHeap ->
    (RiscvPmpBase.coq_Term, coq_SHeap) prod option

  val try_consume_chunk_ptsreg_precise :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg -> coq_SHeap ->
    RiscvPmpBase.coq_Term -> (coq_SHeap, coq_PathCondition) prod option

  val try_consume_chunk_precise :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SHeap ->
    coq_Chunk -> (coq_SHeap, coq_PathCondition) prod option

  val interpret_chunk :
    bi -> coq_PredicateDef -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_Chunk -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env -> __

  val interpret_scchunk : bi -> coq_PredicateDef -> coq_SCChunk -> __

  val interpret_scheap : bi -> coq_PredicateDef -> coq_SCHeap -> __

  type coq_EChunk = RiscvPmpBase.coq_ETerm coq_GChunk

  val coq_Erase_Chunk : (coq_Chunk, coq_EChunk) RiscvPmpBase.coq_Erase

  type coq_World = { wctx : (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
                            Coq_ctx.coq_Ctx;
                     wco : coq_PathCondition }

  val wctx :
    coq_World -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  val wco : coq_World -> coq_PathCondition

  val wnil : coq_World

  val wlctx :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_World

  val wsnoc :
    coq_World -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_World

  val term_var_zero :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> RiscvPmpBase.coq_Term

  val wlet :
    coq_World -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> Coq_ty.coq_Val
    -> coq_World

  val wcat :
    coq_World -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_World

  val wformula : coq_World -> coq_Formula -> coq_World

  val wpathcondition : coq_World -> coq_PathCondition -> coq_World

  val wsubst :
    coq_World -> lVar -> Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> RiscvPmpBase.coq_Term -> coq_World

  val wmatch :
    coq_World -> Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> lVar
    RiscvPmpBase.coq_Pattern -> lVar RiscvPmpBase.coq_PatternCase -> coq_World

  val wmatchvar_patternvars :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar ->
    Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
    -> lVar RiscvPmpBase.coq_Pattern -> lVar RiscvPmpBase.coq_PatternCase ->
    RiscvPmpBase.coq_Sub

  val wmatchvar :
    coq_World -> lVar -> Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> lVar RiscvPmpBase.coq_Pattern ->
    lVar RiscvPmpBase.coq_PatternCase -> coq_World

  type 'a coq_Valid = coq_World -> 'a

  type ('a, 'b) coq_Impl = 'a -> 'b

  type ('i, 'a) coq_Forall = 'i -> 'a

  type coq_Tri =
  | Coq_tri_id
  | Coq_tri_cons of coq_World * lVar * Coq_ty.coq_Ty
     * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
     * RiscvPmpBase.coq_Term * coq_Tri

  val coq_Tri_rect :
    (coq_World -> 'a1) -> (coq_World -> coq_World -> lVar -> Coq_ty.coq_Ty ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    RiscvPmpBase.coq_Term -> coq_Tri -> 'a1 -> 'a1) -> coq_World -> coq_World
    -> coq_Tri -> 'a1

  val coq_Tri_rec :
    (coq_World -> 'a1) -> (coq_World -> coq_World -> lVar -> Coq_ty.coq_Ty ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In ->
    RiscvPmpBase.coq_Term -> coq_Tri -> 'a1 -> 'a1) -> coq_World -> coq_World
    -> coq_Tri -> 'a1

  val tri_comp :
    coq_World -> coq_World -> coq_World -> coq_Tri -> coq_Tri -> coq_Tri

  val sub_wmatch_patctx :
    coq_World -> Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> lVar
    RiscvPmpBase.coq_Pattern -> lVar RiscvPmpBase.coq_PatternCase ->
    RiscvPmpBase.coq_Sub

  val sub_triangular :
    coq_World -> coq_World -> coq_Tri -> RiscvPmpBase.coq_Sub

  val sub_triangular_inv :
    coq_World -> coq_World -> coq_Tri -> RiscvPmpBase.coq_Sub

  type coq_Acc =
  | Coq_acc_refl
  | Coq_acc_sub of coq_World * RiscvPmpBase.coq_Sub

  val coq_Acc_rect :
    coq_World -> 'a1 -> (coq_World -> RiscvPmpBase.coq_Sub -> __ -> 'a1) ->
    coq_World -> coq_Acc -> 'a1

  val coq_Acc_rec :
    coq_World -> 'a1 -> (coq_World -> RiscvPmpBase.coq_Sub -> __ -> 'a1) ->
    coq_World -> coq_Acc -> 'a1

  val acc_trans :
    coq_World -> coq_World -> coq_World -> coq_Acc -> coq_Acc -> coq_Acc

  val sub_acc : coq_World -> coq_World -> coq_Acc -> RiscvPmpBase.coq_Sub

  type 'a coq_Box = coq_World -> coq_Acc -> 'a

  val acc_wnil_init : coq_World -> coq_Acc

  val acc_wlctx_valuation :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env ->
    coq_Acc

  val acc_snoc_right :
    coq_World -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_Acc

  val acc_cat_right :
    coq_World -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_Acc

  val acc_snoc_left :
    coq_World -> coq_World -> coq_Acc -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding -> RiscvPmpBase.coq_Term -> coq_Acc

  val acc_snoc_left' :
    coq_World -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
    RiscvPmpBase.coq_Term -> coq_Acc

  val acc_cat_left :
    coq_World -> coq_World -> coq_Acc -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx -> RiscvPmpBase.coq_Sub -> coq_Acc

  val acc_formula_right : coq_World -> coq_Formula -> coq_Acc

  val acc_pathcondition_right : coq_World -> coq_PathCondition -> coq_Acc

  val acc_subst_right :
    coq_World -> lVar -> Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> RiscvPmpBase.coq_Term -> coq_Acc

  val acc_match_right :
    coq_World -> Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> lVar
    RiscvPmpBase.coq_Pattern -> lVar RiscvPmpBase.coq_PatternCase -> coq_Acc

  val sub_matchvar_right :
    coq_World -> lVar -> Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> lVar RiscvPmpBase.coq_Pattern ->
    lVar RiscvPmpBase.coq_PatternCase -> RiscvPmpBase.coq_Sub

  val acc_matchvar_right :
    coq_World -> lVar -> Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> lVar RiscvPmpBase.coq_Pattern ->
    lVar RiscvPmpBase.coq_PatternCase -> coq_Acc

  val acc_triangular : coq_World -> coq_World -> coq_Tri -> coq_Acc

  val preorder_acc : (coq_World, coq_Acc) preOrder

  val coq_K :
    (('a1, 'a2) coq_Impl coq_Box, ('a1 coq_Box, 'a2 coq_Box) coq_Impl)
    coq_Impl coq_Valid

  val coq_T : ('a1 coq_Box, 'a1) coq_Impl coq_Valid

  val four : ('a1 coq_Box, 'a1 coq_Box coq_Box) coq_Impl coq_Valid

  val valid_box : 'a1 coq_Valid -> 'a1 coq_Box coq_Valid

  val fmap_box :
    ('a1, 'a2) coq_Impl coq_Valid -> ('a1 coq_Box, 'a2 coq_Box) coq_Impl
    coq_Valid

  val extend_box :
    ('a1 coq_Box, 'a2) coq_Impl coq_Valid -> ('a1 coq_Box, 'a2 coq_Box)
    coq_Impl coq_Valid

  val comp :
    (('a2, 'a3) coq_Impl, (('a1, 'a2) coq_Impl, ('a1, 'a3) coq_Impl)
    coq_Impl) coq_Impl coq_Valid

  module ModalNotations :
   sig
   end

  type 'a coq_Persistent = ('a, 'a coq_Box) coq_Impl coq_Valid

  val persist : 'a1 coq_Persistent -> ('a1, 'a1 coq_Box) coq_Impl coq_Valid

  val persistent_box : 'a1 coq_Box coq_Persistent

  val persistent_subst : 'a1 RiscvPmpBase.coq_Subst -> 'a1 coq_Persistent

  type coq_Pred = __

  type 'a coq_Tm = 'a

  val bi_pred : coq_World -> bi

  type 't coq_InstPred =
  | MkInstPred

  val instpred_option :
    'a1 coq_InstPred -> 'a1 RiscvPmpBase.coq_Option coq_InstPred

  val instpred_pair :
    'a1 coq_InstPred -> 'a2 coq_InstPred -> ('a1, 'a2) RiscvPmpBase.coq_Pair
    coq_InstPred

  val instpred_ctx_inst : 'a1 coq_InstPred -> 'a1 Coq_ctx.coq_Ctx coq_InstPred

  val instpred_inst_formula : coq_Formula coq_InstPred

  type coq_Solver =
    coq_World -> coq_PathCondition -> (coq_World, (coq_Tri,
    coq_PathCondition) prod) sigT option

  val solver_null : coq_Solver

  type coq_SolverUserOnly =
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    purePredicate -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) Coq_env.coq_Env
    -> coq_PathCondition RiscvPmpBase.coq_Option

  val simplify_all :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (coq_Formula
    -> coq_PathCondition -> coq_PathCondition option) -> coq_PathCondition ->
    coq_PathCondition -> coq_PathCondition option

  val solveruseronly_simplify_formula :
    coq_SolverUserOnly -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> coq_Formula -> coq_PathCondition -> coq_PathCondition
    option

  val solveruseronly_to_solver : coq_SolverUserOnly -> coq_Solver

  val solver_compose : coq_Solver -> coq_Solver -> coq_Solver

  module DList :
   sig
    type coq_DList = { raw : (coq_PathCondition -> coq_PathCondition
                             RiscvPmpBase.coq_Option) }

    val raw :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DList
      -> coq_PathCondition -> coq_PathCondition RiscvPmpBase.coq_Option

    val instpred_dlist : coq_DList coq_InstPred

    val singleton :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_DList

    val run :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DList
      -> coq_PathCondition RiscvPmpBase.coq_Option

    val error :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DList

    val empty :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DList

    val cat :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DList
      -> coq_DList -> coq_DList
   end

  val is_off :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_Term -> coq_Formula

  val is_on :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_Term -> coq_Formula

  val is_TOR :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_Term -> coq_Formula

  val is_machine_mode :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_Term -> coq_Formula

  val fml_pmp_match_conditions :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
    -> RiscvPmpBase.coq_Term -> coq_Formula

  val fml_pmp_match :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
    -> RiscvPmpBase.coq_Term -> (Coq_ty.recordf, Coq_ty.coq_Ty,
    RiscvPmpBase.coq_Term) namedEnv -> RiscvPmpBase.coq_Term ->
    RiscvPmpBase.coq_Term -> coq_Formula

  val fml_pmp_nomatch_conditions :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
    -> RiscvPmpBase.coq_Term -> coq_Formula

  val fml_pmp_nomatch :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
    -> RiscvPmpBase.coq_Term -> (Coq_ty.recordf, Coq_ty.coq_Ty,
    RiscvPmpBase.coq_Term) namedEnv -> RiscvPmpBase.coq_Term ->
    RiscvPmpBase.coq_Term -> coq_Formula -> coq_Formula

  val cfg_to_env :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> pmpcfg_ent
    -> (Coq_ty.recordf, Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) namedEnv

  val simplify_pmpcheck_pure_list :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
    -> pmpEntryCfg list -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
    coq_Formula

  val simplify_pmpcheck :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
    -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_ListView ->
    RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> coq_Formula option

  val simplify_pmpcheck_term_list :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
    -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
    RiscvPmpBase.coq_Term -> coq_Formula option

  val pmp_check_fml_term_aux :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
    -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
    RiscvPmpBase.coq_Term -> coq_Formula

  val pmp_check_fml_aux :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Val -> Coq_ty.coq_Val -> Coq_ty.coq_Val -> Coq_ty.coq_Val list
    -> Coq_ty.coq_Val -> Coq_ty.coq_Val -> coq_Formula

  val simplify_sub_perm :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> coq_PathCondition option

  val simplify_access_pmp_perm :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> coq_PathCondition option

  val simplify_gen_pmp_access :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
    -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
    RiscvPmpBase.coq_Term -> coq_PathCondition option

  val simplify_pmp_access :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
    -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> coq_PathCondition
    option

  val simplify_pmp_check_rwx :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> coq_PathCondition option

  val simplify_pmp_check_perms :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
    -> coq_PathCondition option

  val simplify_within_cfg :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
    -> RiscvPmpBase.coq_Term -> coq_PathCondition option

  val simplify_prev_addr :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
    -> coq_PathCondition option

  val simplify_user :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> _UU1d477_ ->
    (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) Coq_env.coq_Env ->
    coq_PathCondition option

  val solver : coq_Solver

  type coq_Message = { msg_function : string; msg_message : string;
                       msg_program_context : (pVar, Coq_ty.coq_Ty)
                                             Binding.coq_Binding
                                             Coq_ctx.coq_Ctx;
                       msg_localstore : RiscvPmpBase.coq_SStore;
                       msg_heap : coq_SHeap;
                       msg_pathcondition : coq_PathCondition }

  val msg_function :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Message
    -> string

  val msg_message :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Message
    -> string

  val msg_program_context :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Message
    -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  val msg_localstore :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Message
    -> RiscvPmpBase.coq_SStore

  val msg_heap :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Message
    -> coq_SHeap

  val msg_pathcondition :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Message
    -> coq_PathCondition

  type coq_EMessage = { emsg_function : string; emsg_message : string;
                        emsg_program_context : (pVar, Coq_ty.coq_Ty)
                                               Binding.coq_Binding
                                               Coq_ctx.coq_Ctx;
                        emsg_localstore : (pVar, Coq_ty.coq_Ty,
                                          RiscvPmpBase.coq_ETerm) namedEnv;
                        emsg_heap : coq_EChunk list;
                        emsg_pathcondition : coq_EFormula list }

  val emsg_function : coq_EMessage -> string

  val emsg_message : coq_EMessage -> string

  val emsg_program_context :
    coq_EMessage -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  val emsg_localstore :
    coq_EMessage -> (pVar, Coq_ty.coq_Ty, RiscvPmpBase.coq_ETerm) namedEnv

  val emsg_heap : coq_EMessage -> coq_EChunk list

  val emsg_pathcondition : coq_EMessage -> coq_EFormula list

  val coq_EraseMessage : (coq_Message, coq_EMessage) RiscvPmpBase.coq_Erase

  val coq_SubstMessage : coq_Message RiscvPmpBase.coq_Subst

  val coq_SubstSUMessage :
    'a1 RiscvPmpBase.coq_SubstUniv -> ('a1, coq_Message)
    RiscvPmpBase.coq_SubstSU

  val coq_SubstLawsMessage : coq_Message RiscvPmpBase.coq_SubstLaws

  val coq_OccursCheckMessage : coq_Message RiscvPmpBase.coq_OccursCheck

  val coq_GenOccursCheckMessage :
    (RiscvPmpBase.coq_WeakensTo, coq_Message) RiscvPmpBase.coq_GenOccursCheck

  val coq_Error_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Message
    -> 'a1

  val coq_Error_rec :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Message
    -> 'a1

  val coq_Obligation_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_Formula -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env ->
    (__ -> 'a1) -> 'a1

  val coq_Obligation_rec :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_Formula -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env ->
    (__ -> 'a1) -> 'a1

  val coq_Debug_rect :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 -> (__
    -> 'a2) -> 'a2

  val coq_Debug_rec :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1 -> (__
    -> 'a2) -> 'a2

  module SymProp :
   sig
    type coq_SymProp =
    | Coq_angelic_binary of coq_SymProp * coq_SymProp
    | Coq_demonic_binary of coq_SymProp * coq_SymProp
    | Coq_error of RiscvPmpBase.Coq_amsg.coq_AMessage
    | Coq_block
    | Coq_assertk of coq_Formula * RiscvPmpBase.Coq_amsg.coq_AMessage
       * coq_SymProp
    | Coq_assumek of coq_Formula * coq_SymProp
    | Coq_angelicv of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding * coq_SymProp
    | Coq_demonicv of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding * coq_SymProp
    | Coq_assert_vareq of lVar * Coq_ty.coq_Ty
       * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
       * RiscvPmpBase.coq_Term * RiscvPmpBase.Coq_amsg.coq_AMessage
       * coq_SymProp
    | Coq_assume_vareq of lVar * Coq_ty.coq_Ty
       * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
       * RiscvPmpBase.coq_Term * coq_SymProp
    | Coq_pattern_match of Coq_ty.coq_Ty * RiscvPmpBase.coq_Term
       * lVar RiscvPmpBase.coq_Pattern
       * (lVar RiscvPmpBase.coq_PatternCase -> coq_SymProp)
    | Coq_pattern_match_var of lVar * Coq_ty.coq_Ty
       * (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In
       * lVar RiscvPmpBase.coq_Pattern
       * (lVar RiscvPmpBase.coq_PatternCase -> coq_SymProp)
    | Coq_debug of RiscvPmpBase.Coq_amsg.coq_AMessage * coq_SymProp

    val coq_SymProp_rect :
      ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SymProp -> 'a1 -> coq_SymProp -> 'a1 -> 'a1) -> ((lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SymProp ->
      'a1 -> coq_SymProp -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.Coq_amsg.coq_AMessage -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Formula ->
      RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_SymProp -> 'a1 -> 'a1) ->
      ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_SymProp -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding -> coq_SymProp -> 'a1 -> 'a1) -> ((lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> coq_SymProp -> 'a1 -> 'a1) ->
      ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar ->
      Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_SymProp -> 'a1 -> 'a1) ->
      ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar ->
      Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> RiscvPmpBase.coq_Term -> coq_SymProp -> 'a1 -> 'a1)
      -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> lVar RiscvPmpBase.coq_Pattern
      -> (lVar RiscvPmpBase.coq_PatternCase -> coq_SymProp) -> (lVar
      RiscvPmpBase.coq_PatternCase -> 'a1) -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar -> Coq_ty.coq_Ty -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> lVar
      RiscvPmpBase.coq_Pattern -> (lVar RiscvPmpBase.coq_PatternCase ->
      coq_SymProp) -> (lVar RiscvPmpBase.coq_PatternCase -> 'a1) -> 'a1) ->
      ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_SymProp -> 'a1 -> 'a1) ->
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SymProp -> 'a1

    val coq_SymProp_rec :
      ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SymProp -> 'a1 -> coq_SymProp -> 'a1 -> 'a1) -> ((lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SymProp ->
      'a1 -> coq_SymProp -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.Coq_amsg.coq_AMessage -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Formula ->
      RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_SymProp -> 'a1 -> 'a1) ->
      ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_SymProp -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding -> coq_SymProp -> 'a1 -> 'a1) -> ((lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> coq_SymProp -> 'a1 -> 'a1) ->
      ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar ->
      Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_SymProp -> 'a1 -> 'a1) ->
      ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar ->
      Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> RiscvPmpBase.coq_Term -> coq_SymProp -> 'a1 -> 'a1)
      -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> lVar RiscvPmpBase.coq_Pattern
      -> (lVar RiscvPmpBase.coq_PatternCase -> coq_SymProp) -> (lVar
      RiscvPmpBase.coq_PatternCase -> 'a1) -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar -> Coq_ty.coq_Ty -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In -> lVar
      RiscvPmpBase.coq_Pattern -> (lVar RiscvPmpBase.coq_PatternCase ->
      coq_SymProp) -> (lVar RiscvPmpBase.coq_PatternCase -> 'a1) -> 'a1) ->
      ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_SymProp -> 'a1 -> 'a1) ->
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SymProp -> 'a1

    val trunc :
      nat -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SymProp -> coq_SymProp

    val angelic_close0 :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SymProp ->
      coq_SymProp

    val demonic_close0 :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_SymProp ->
      coq_SymProp

    val demonic_close :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SymProp -> coq_SymProp

    val angelic_list' :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SymProp -> ('a1 -> coq_SymProp) -> 'a1 RiscvPmpBase.coq_List ->
      coq_SymProp

    val angelic_list :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.Coq_amsg.coq_AMessage -> ('a1 -> coq_SymProp) -> 'a1
      RiscvPmpBase.coq_List -> coq_SymProp

    val demonic_list' :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_SymProp -> ('a1 -> coq_SymProp) -> 'a1 RiscvPmpBase.coq_List ->
      coq_SymProp

    val demonic_list :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1 ->
      coq_SymProp) -> 'a1 RiscvPmpBase.coq_List -> coq_SymProp

    val angelic_finite :
      ('a1, 'a1) relDecision -> 'a1 finite -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.Coq_amsg.coq_AMessage -> ('a1 -> coq_SymProp) ->
      coq_SymProp

    val demonic_finite :
      ('a1, 'a1) relDecision -> 'a1 finite -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1 -> coq_SymProp) ->
      coq_SymProp

    val angelic_pattern_match :
      Coq_ty.coq_Ty -> lVar RiscvPmpBase.coq_Pattern -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> RiscvPmpBase.coq_Term -> (lVar
      RiscvPmpBase.coq_PatternCase -> coq_SymProp) -> coq_SymProp

    val angelic_pattern_match_var :
      Coq_ty.coq_Ty -> lVar RiscvPmpBase.coq_Pattern -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> (lVar
      RiscvPmpBase.coq_PatternCase -> coq_SymProp) -> coq_SymProp

    val demonic_pattern_match :
      Coq_ty.coq_Ty -> lVar RiscvPmpBase.coq_Pattern -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> RiscvPmpBase.coq_Term -> (lVar
      RiscvPmpBase.coq_PatternCase -> coq_SymProp) -> coq_SymProp

    val demonic_pattern_match_var :
      Coq_ty.coq_Ty -> lVar RiscvPmpBase.coq_Pattern -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> (lVar
      RiscvPmpBase.coq_PatternCase -> coq_SymProp) -> coq_SymProp

    val assume_pathcondition_without_solver' :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_PathCondition -> coq_SymProp -> coq_SymProp

    val assert_pathcondition_without_solver' :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_PathCondition -> coq_SymProp
      -> coq_SymProp

    val assume_pathcondition_without_solver :
      coq_World -> coq_PathCondition -> coq_SymProp -> coq_SymProp

    val assert_pathcondition_without_solver :
      coq_World -> RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_PathCondition ->
      coq_SymProp -> coq_SymProp

    val assume_triangular :
      coq_World -> coq_World -> coq_Tri -> coq_SymProp -> coq_SymProp

    val assert_triangular :
      coq_World -> coq_World -> RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_Tri
      -> (RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_SymProp) -> coq_SymProp

    module Coq_notations :
     sig
     end

    module Statistics :
     sig
      val size :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_SymProp -> n

      type coq_Count = { block : n; error : n; debug : n }

      val block : coq_Count -> n

      val error : coq_Count -> n

      val debug : coq_Count -> n

      val empty : coq_Count

      val inc_block : coq_Count -> coq_Count

      val inc_error : coq_Count -> coq_Count

      val inc_debug : coq_Count -> coq_Count

      val count_nodes :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_SymProp -> coq_Count -> coq_Count

      val count_to_stats : coq_Count -> stats
     end
   end

  module Postprocessing :
   sig
    type ('m1, 'm2) coq_AngelicBinaryFailMsg = { angelic_binary_failmsg_left : 
                                                 'm1;
                                                 angelic_binary_failmsg_right : 
                                                 'm2 }

    val angelic_binary_failmsg_left :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, 'a2)
      coq_AngelicBinaryFailMsg -> 'a1

    val angelic_binary_failmsg_right :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, 'a2)
      coq_AngelicBinaryFailMsg -> 'a2

    val coq_SubstAngelicBinaryFailMsg :
      'a1 RiscvPmpBase.coq_Subst -> 'a2 RiscvPmpBase.coq_Subst -> ('a1, 'a2)
      coq_AngelicBinaryFailMsg RiscvPmpBase.coq_Subst

    val coq_SubstSUAngelicBinaryFailMsg :
      ('a1, 'a2) RiscvPmpBase.coq_SubstSU -> ('a1, 'a3)
      RiscvPmpBase.coq_SubstSU -> ('a1, ('a2, 'a3) coq_AngelicBinaryFailMsg)
      RiscvPmpBase.coq_SubstSU

    val coq_SubstLawsAngelicBinaryFailMsg :
      'a1 RiscvPmpBase.coq_Subst -> 'a1 RiscvPmpBase.coq_SubstLaws -> 'a2
      RiscvPmpBase.coq_Subst -> 'a2 RiscvPmpBase.coq_SubstLaws -> ('a1, 'a2)
      coq_AngelicBinaryFailMsg RiscvPmpBase.coq_SubstLaws

    val coq_OccursCheckAngelicBinaryFailMsg :
      'a1 RiscvPmpBase.coq_OccursCheck -> 'a2 RiscvPmpBase.coq_OccursCheck ->
      ('a1, 'a2) coq_AngelicBinaryFailMsg RiscvPmpBase.coq_OccursCheck

    val coq_GenOccursCheckAngelicBinaryFailMsg :
      (RiscvPmpBase.coq_WeakensTo, 'a1) RiscvPmpBase.coq_SubstSU -> 'a1
      RiscvPmpBase.coq_Subst -> (RiscvPmpBase.coq_WeakensTo, 'a2)
      RiscvPmpBase.coq_SubstSU -> 'a2 RiscvPmpBase.coq_Subst ->
      (RiscvPmpBase.coq_WeakensTo, 'a1) RiscvPmpBase.coq_GenOccursCheck ->
      (RiscvPmpBase.coq_WeakensTo, 'a2) RiscvPmpBase.coq_GenOccursCheck ->
      (RiscvPmpBase.coq_WeakensTo, ('a1, 'a2) coq_AngelicBinaryFailMsg)
      RiscvPmpBase.coq_GenOccursCheck

    type ('mE1, 'mE2) coq_EAngelicBinaryFailMsg =
    | MkEAngelicBinaryFailMsg of 'mE1 * 'mE2

    val coq_EAngelicBinaryFailMsg_rect :
      ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) coq_EAngelicBinaryFailMsg -> 'a3

    val coq_EAngelicBinaryFailMsg_rec :
      ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) coq_EAngelicBinaryFailMsg -> 'a3

    val coq_EraseAngelicBinaryFailMsg :
      ('a1, 'a2) RiscvPmpBase.coq_Erase -> ('a3, 'a4) RiscvPmpBase.coq_Erase
      -> (('a1, 'a3) coq_AngelicBinaryFailMsg, ('a2, 'a4)
      coq_EAngelicBinaryFailMsg) RiscvPmpBase.coq_Erase

    val angelic_binary_prune :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> SymProp.coq_SymProp -> SymProp.coq_SymProp

    val demonic_binary_prune :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> SymProp.coq_SymProp -> SymProp.coq_SymProp

    val assertk_prune :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> RiscvPmpBase.Coq_amsg.coq_AMessage ->
      SymProp.coq_SymProp -> SymProp.coq_SymProp

    val assumek_prune :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> SymProp.coq_SymProp -> SymProp.coq_SymProp

    val angelicv_prune :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> SymProp.coq_SymProp ->
      SymProp.coq_SymProp

    val demonicv_prune :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> SymProp.coq_SymProp ->
      SymProp.coq_SymProp

    val assume_vareq_prune :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar ->
      Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> RiscvPmpBase.coq_Term -> SymProp.coq_SymProp ->
      SymProp.coq_SymProp

    val assert_vareq_prune :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar ->
      Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.Coq_amsg.coq_AMessage -> SymProp.coq_SymProp ->
      SymProp.coq_SymProp

    val prune :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> SymProp.coq_SymProp

    module SolveEvars :
     sig
      val assert_msgs_formulas :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (RiscvPmpBase.Coq_amsg.coq_AMessage, coq_Formula)
        RiscvPmpBase.coq_Pair Coq_ctx.coq_Ctx -> SymProp.coq_SymProp ->
        SymProp.coq_SymProp

      type coq_ECtx =
      | Coq_ectx of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
         * (RiscvPmpBase.Coq_amsg.coq_AMessage, coq_Formula)
           RiscvPmpBase.coq_Pair Coq_ctx.coq_Ctx

      val coq_ECtx_rect :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ((lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (RiscvPmpBase.Coq_amsg.coq_AMessage, coq_Formula)
        RiscvPmpBase.coq_Pair Coq_ctx.coq_Ctx -> 'a1) -> (lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_ECtx -> 'a1

      val coq_ECtx_rec :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ((lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        (RiscvPmpBase.Coq_amsg.coq_AMessage, coq_Formula)
        RiscvPmpBase.coq_Pair Coq_ctx.coq_Ctx -> 'a1) -> (lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_ECtx -> 'a1

      val ectx_refl :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_ECtx

      val ectx_formula :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_ECtx ->
        RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_Formula -> coq_ECtx

      val ectx_snoc :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_ECtx ->
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_ECtx

      val ectx_subst :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_ECtx ->
        lVar -> Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_In -> RiscvPmpBase.coq_Term -> coq_ECtx option

      val plug :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_ECtx ->
        SymProp.coq_SymProp -> SymProp.coq_SymProp

      val plug_msg :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_ECtx ->
        RiscvPmpBase.Coq_amsg.coq_AMessage ->
        RiscvPmpBase.Coq_amsg.coq_AMessage

      val push :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_ECtx ->
        SymProp.coq_SymProp -> SymProp.coq_SymProp
     end

    val solve_evars :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> SymProp.coq_SymProp

    module SolveUvars :
     sig
      val assume_pathcondition :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_PathCondition -> SymProp.coq_SymProp -> SymProp.coq_SymProp

      type coq_UCtx =
      | Coq_uctx of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
         * coq_PathCondition

      val coq_UCtx_rect :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ((lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_PathCondition -> 'a1) -> (lVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_UCtx -> 'a1

      val coq_UCtx_rec :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ((lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_PathCondition -> 'a1) -> (lVar, Coq_ty.coq_Ty)
        Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_UCtx -> 'a1

      val uctx_refl :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_UCtx

      val uctx_formula :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_UCtx ->
        coq_Formula -> coq_UCtx

      val uctx_snoc :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_UCtx ->
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_UCtx

      val uctx_subst :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_UCtx ->
        lVar -> Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
        Coq_ctx.coq_In -> RiscvPmpBase.coq_Term -> coq_UCtx option

      val plug :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_UCtx ->
        SymProp.coq_SymProp -> SymProp.coq_SymProp

      val plug_error :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_UCtx ->
        RiscvPmpBase.Coq_amsg.coq_AMessage -> SymProp.coq_SymProp

      val push :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_UCtx ->
        SymProp.coq_SymProp -> SymProp.coq_SymProp
     end

    val solve_uvars :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> SymProp.coq_SymProp

    module Experimental :
     sig
      type coq_Ephemeral = (SolveEvars.coq_ECtx, SolveUvars.coq_UCtx) sum

      type coq_EProp =
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_Ephemeral -> SymProp.coq_SymProp

      val angelic_binary :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_EProp -> coq_EProp -> coq_EProp

      val angelicv :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
        Coq_ty.coq_Ty) Binding.coq_Binding -> coq_EProp -> coq_EProp

      val demonic_binary :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        coq_EProp -> coq_EProp -> coq_EProp

      val error :
        (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_EProp
     end

    val weaken_symprop :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> RiscvPmpBase.coq_WeakensTo -> SymProp.coq_SymProp

    val coq_SubstSU_SymProp :
      (RiscvPmpBase.coq_WeakensTo, SymProp.coq_SymProp)
      RiscvPmpBase.coq_SubstSU

    type coq_UQSymProp =
      (RiscvPmpBase.coq_WeakensTo, SymProp.coq_SymProp)
      RiscvPmpBase.coq_Weakened

    val from_uqSymProp :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_UQSymProp -> SymProp.coq_SymProp

    val uq_angelic_binary :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_UQSymProp -> coq_UQSymProp -> coq_UQSymProp

    val uq_demonic_binary :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_UQSymProp -> coq_UQSymProp -> coq_UQSymProp

    val uq_error :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_UQSymProp

    val uq_block :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_UQSymProp

    val uq_assertk :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_UQSymProp ->
      coq_UQSymProp

    val uq_assumek :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_UQSymProp -> coq_UQSymProp

    val uq_angelicv :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> coq_UQSymProp -> coq_UQSymProp

    val uq_demonicv :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> coq_UQSymProp -> coq_UQSymProp

    val uq_assert_vareq :
      lVar -> Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_UQSymProp -> coq_UQSymProp

    val uq_assume_vareq :
      lVar -> Coq_ty.coq_Ty -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> RiscvPmpBase.coq_Term -> coq_UQSymProp ->
      coq_UQSymProp

    val uq_debug :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_UQSymProp -> coq_UQSymProp

    val to_uqSymProp :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> coq_UQSymProp

    val unquantify :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> SymProp.coq_SymProp

    val weakenWorld :
      coq_World -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
      -> RiscvPmpBase.coq_WeakensTo -> coq_World

    val weakenWorld_acc :
      coq_World -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
      -> RiscvPmpBase.coq_WeakensTo -> coq_Acc
   end

  val postprocess :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    SymProp.coq_SymProp -> SymProp.coq_SymProp

  val postprocess2 :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    SymProp.coq_SymProp -> SymProp.coq_SymProp

  module Erasure :
   sig
    type coq_ESymProp =
    | Coq_eangelic_binary of coq_ESymProp * coq_ESymProp
    | Coq_edemonic_binary of coq_ESymProp * coq_ESymProp
    | Coq_eerror of RiscvPmpBase.Coq_amsg.coq_EAMessage
    | Coq_eblock
    | Coq_eassertk of coq_EFormula * coq_ESymProp
    | Coq_eassumek of coq_EFormula * coq_ESymProp
    | Coq_eangelicv of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
       * coq_ESymProp
    | Coq_edemonicv of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
       * coq_ESymProp
    | Coq_eassert_vareq of lVar * Coq_ty.coq_Ty * nat
       * RiscvPmpBase.coq_ETerm * coq_ESymProp
    | Coq_eassume_vareq of lVar * Coq_ty.coq_Ty * nat
       * RiscvPmpBase.coq_ETerm * coq_ESymProp
    | Coq_epattern_match of Coq_ty.coq_Ty * RiscvPmpBase.coq_ETerm
       * lVar RiscvPmpBase.coq_Pattern
       * (lVar RiscvPmpBase.coq_PatternCase -> coq_ESymProp)
    | Coq_epattern_match_var of lVar * Coq_ty.coq_Ty * nat
       * lVar RiscvPmpBase.coq_Pattern
       * (lVar RiscvPmpBase.coq_PatternCase -> coq_ESymProp)
    | Coq_edebug of (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
       * RiscvPmpBase.Coq_amsg.coq_AMessage * coq_ESymProp

    val coq_ESymProp_rect :
      (coq_ESymProp -> 'a1 -> coq_ESymProp -> 'a1 -> 'a1) -> (coq_ESymProp ->
      'a1 -> coq_ESymProp -> 'a1 -> 'a1) ->
      (RiscvPmpBase.Coq_amsg.coq_EAMessage -> 'a1) -> 'a1 -> (coq_EFormula ->
      coq_ESymProp -> 'a1 -> 'a1) -> (coq_EFormula -> coq_ESymProp -> 'a1 ->
      'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_ESymProp ->
      'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
      coq_ESymProp -> 'a1 -> 'a1) -> (lVar -> Coq_ty.coq_Ty -> nat ->
      RiscvPmpBase.coq_ETerm -> coq_ESymProp -> 'a1 -> 'a1) -> (lVar ->
      Coq_ty.coq_Ty -> nat -> RiscvPmpBase.coq_ETerm -> coq_ESymProp -> 'a1
      -> 'a1) -> (Coq_ty.coq_Ty -> RiscvPmpBase.coq_ETerm -> lVar
      RiscvPmpBase.coq_Pattern -> (lVar RiscvPmpBase.coq_PatternCase ->
      coq_ESymProp) -> (lVar RiscvPmpBase.coq_PatternCase -> 'a1) -> 'a1) ->
      (lVar -> Coq_ty.coq_Ty -> nat -> lVar RiscvPmpBase.coq_Pattern -> (lVar
      RiscvPmpBase.coq_PatternCase -> coq_ESymProp) -> (lVar
      RiscvPmpBase.coq_PatternCase -> 'a1) -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_ESymProp -> 'a1 -> 'a1) ->
      coq_ESymProp -> 'a1

    val coq_ESymProp_rec :
      (coq_ESymProp -> 'a1 -> coq_ESymProp -> 'a1 -> 'a1) -> (coq_ESymProp ->
      'a1 -> coq_ESymProp -> 'a1 -> 'a1) ->
      (RiscvPmpBase.Coq_amsg.coq_EAMessage -> 'a1) -> 'a1 -> (coq_EFormula ->
      coq_ESymProp -> 'a1 -> 'a1) -> (coq_EFormula -> coq_ESymProp -> 'a1 ->
      'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> coq_ESymProp ->
      'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding ->
      coq_ESymProp -> 'a1 -> 'a1) -> (lVar -> Coq_ty.coq_Ty -> nat ->
      RiscvPmpBase.coq_ETerm -> coq_ESymProp -> 'a1 -> 'a1) -> (lVar ->
      Coq_ty.coq_Ty -> nat -> RiscvPmpBase.coq_ETerm -> coq_ESymProp -> 'a1
      -> 'a1) -> (Coq_ty.coq_Ty -> RiscvPmpBase.coq_ETerm -> lVar
      RiscvPmpBase.coq_Pattern -> (lVar RiscvPmpBase.coq_PatternCase ->
      coq_ESymProp) -> (lVar RiscvPmpBase.coq_PatternCase -> 'a1) -> 'a1) ->
      (lVar -> Coq_ty.coq_Ty -> nat -> lVar RiscvPmpBase.coq_Pattern -> (lVar
      RiscvPmpBase.coq_PatternCase -> coq_ESymProp) -> (lVar
      RiscvPmpBase.coq_PatternCase -> 'a1) -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.Coq_amsg.coq_AMessage -> coq_ESymProp -> 'a1 -> 'a1) ->
      coq_ESymProp -> 'a1

    val erase_symprop :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> coq_ESymProp

    val erase_SymProp :
      (SymProp.coq_SymProp, coq_ESymProp) RiscvPmpBase.coq_Erase

    val erase_valuation :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ((lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env ->
      (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list

    val erase_Valuation :
      (((lVar, Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val)
      Coq_env.coq_Env, (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list)
      RiscvPmpBase.coq_Erase

    val inst_env' :
      (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list -> (Coq_ty.coq_Ty ->
      RiscvPmpBase.coq_ETerm -> Coq_ty.coq_Val option) -> Coq_ty.coq_Ty
      Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_ETerm)
      Coq_env.coq_Env -> (Coq_ty.coq_Ty, Coq_ty.coq_Val) Coq_env.coq_Env
      option

    val inst_namedenv' :
      (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list -> (Coq_ty.coq_Ty ->
      RiscvPmpBase.coq_ETerm -> Coq_ty.coq_Val option) -> ('a1,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1,
      Coq_ty.coq_Ty, RiscvPmpBase.coq_ETerm) namedEnv -> ('a1, Coq_ty.coq_Ty,
      Coq_ty.coq_Val) namedEnv option

    val inst_eterm :
      (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list -> Coq_ty.coq_Ty ->
      RiscvPmpBase.coq_ETerm -> Coq_ty.coq_Val option

    val inst_namedenv :
      (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list -> ('a1, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty,
      RiscvPmpBase.coq_ETerm) namedEnv -> ('a1, Coq_ty.coq_Ty,
      Coq_ty.coq_Val) namedEnv option

    val inst_env :
      (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list -> Coq_ty.coq_Ty
      Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_ETerm)
      Coq_env.coq_Env -> (Coq_ty.coq_Ty, Coq_ty.coq_Val) Coq_env.coq_Env
      option

    val inst_eformula :
      (Coq_ty.coq_Ty, Coq_ty.coq_Val) sigT list -> coq_EFormula -> __ option

    val list_remove : 'a1 list -> nat -> 'a1 list

    module Coq_notations :
     sig
     end
   end

  module Coq_notations :
   sig
   end

  val modality_assuming : coq_World -> coq_World -> coq_Acc -> modality

  val modality_forgetting : coq_World -> coq_World -> coq_Acc -> modality

  module Coq_logicalrelation :
   sig
    type ('aT, 'a) coq_Rel = { coq_RSat : ('a -> ('aT, coq_Pred) coq_Impl
                                          coq_Valid) }

    val coq_RInst : ('a1, 'a2) RiscvPmpBase.coq_Inst -> ('a1, 'a2) coq_Rel

    val coq_RInstPropIff : 'a1 coq_InstPred -> ('a1, __) coq_Rel

    val coq_RBox : ('a1, 'a2) coq_Rel -> ('a1 coq_Box, 'a2) coq_Rel

    val coq_RImpl :
      ('a1, 'a2) coq_Rel -> ('a3, 'a4) coq_Rel -> (('a1, 'a3) coq_Impl, 'a2
      -> 'a4) coq_Rel

    val coq_RForall :
      ('a1 -> ('a2, 'a3) coq_Rel) -> (('a1, 'a2) coq_Forall, 'a1 -> 'a3)
      coq_Rel

    val coq_RVal :
      Coq_ty.coq_Ty -> (RiscvPmpBase.coq_Term, Coq_ty.coq_Val) coq_Rel

    val coq_RNEnv :
      ('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (('a1,
      Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) namedEnv, ('a1, Coq_ty.coq_Ty,
      Coq_ty.coq_Val) namedEnv) coq_Rel

    val coq_REnv :
      Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> ((Coq_ty.coq_Ty,
      RiscvPmpBase.coq_Term) Coq_env.coq_Env, (Coq_ty.coq_Ty, Coq_ty.coq_Val)
      Coq_env.coq_Env) coq_Rel

    val coq_RUnit : (RiscvPmpBase.coq_Unit, unit0) coq_Rel

    val coq_RPathCondition : (coq_PathCondition, __) coq_Rel

    val coq_RFormula : (coq_Formula, __) coq_Rel

    val coq_RChunk : (coq_Chunk, coq_SCChunk) coq_Rel

    val coq_RMsg : ('a2, 'a3) coq_Rel -> (('a1, 'a2) coq_Impl, 'a3) coq_Rel

    val coq_RList : ('a1, 'a2) coq_Rel -> ('a1 list, 'a2 list) coq_Rel

    val coq_RHeap : (coq_SHeap, coq_SCHeap) coq_Rel

    val coq_RConst : ('a1 RiscvPmpBase.coq_Const, 'a1) coq_Rel

    val coq_RProd :
      ('a1, 'a2) coq_Rel -> ('a3, 'a4) coq_Rel -> (('a1, 'a3) prod, ('a2,
      'a4) prod) coq_Rel

    val coq_RMatchResult :
      Coq_ty.coq_Ty -> 'a1 RiscvPmpBase.coq_Pattern -> ('a1
      RiscvPmpBase.coq_SMatchResult, 'a1 RiscvPmpBase.coq_MatchResult) coq_Rel

    val coq_RIn :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In, Coq_ty.coq_Val) coq_Rel

    module Coq_notations :
     sig
     end
   end

  module RSolve :
   sig
   end

  module AutorewriteUnifLogic :
   sig
   end

  module LogicalSoundness :
   sig
    val coq_RProp : (SymProp.coq_SymProp, __) Coq_logicalrelation.coq_Rel
   end

  module Coq_asn :
   sig
    type coq_Assertion =
    | Coq_formula of coq_Formula
    | Coq_chunk of coq_Chunk
    | Coq_chunk_angelic of coq_Chunk
    | Coq_pattern_match of Coq_ty.coq_Ty * RiscvPmpBase.coq_Term
       * lVar RiscvPmpBase.coq_Pattern
       * (lVar RiscvPmpBase.coq_PatternCase -> coq_Assertion)
    | Coq_sep of coq_Assertion * coq_Assertion
    | Coq_or of coq_Assertion * coq_Assertion
    | Coq_exist of lVar * Coq_ty.coq_Ty * coq_Assertion
    | Coq_debug

    val coq_Assertion_rect :
      ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> coq_Chunk -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Chunk -> 'a1) -> ((lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
      RiscvPmpBase.coq_Term -> lVar RiscvPmpBase.coq_Pattern -> (lVar
      RiscvPmpBase.coq_PatternCase -> coq_Assertion) -> (lVar
      RiscvPmpBase.coq_PatternCase -> 'a1) -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Assertion -> 'a1 ->
      coq_Assertion -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Assertion -> 'a1 ->
      coq_Assertion -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar -> Coq_ty.coq_Ty ->
      coq_Assertion -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1) -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Assertion -> 'a1

    val coq_Assertion_rec :
      ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> 'a1) -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> coq_Chunk -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Chunk -> 'a1) -> ((lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
      RiscvPmpBase.coq_Term -> lVar RiscvPmpBase.coq_Pattern -> (lVar
      RiscvPmpBase.coq_PatternCase -> coq_Assertion) -> (lVar
      RiscvPmpBase.coq_PatternCase -> 'a1) -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Assertion -> 'a1 ->
      coq_Assertion -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Assertion -> 'a1 ->
      coq_Assertion -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar -> Coq_ty.coq_Ty ->
      coq_Assertion -> 'a1 -> 'a1) -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1) -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Assertion -> 'a1

    val match_bool :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> coq_Assertion -> coq_Assertion -> coq_Assertion

    val match_enum :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.enumi -> RiscvPmpBase.coq_Term -> (Coq_ty.enumt ->
      coq_Assertion) -> coq_Assertion

    val match_sum :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> lVar ->
      coq_Assertion -> lVar -> coq_Assertion -> coq_Assertion

    val match_list :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> coq_Assertion -> lVar -> lVar
      -> coq_Assertion -> coq_Assertion

    val match_prod :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> lVar -> lVar
      -> coq_Assertion -> coq_Assertion

    val match_tuple :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> RiscvPmpBase.coq_Term -> lVar
      RiscvPmpBase.coq_TuplePat -> coq_Assertion -> coq_Assertion

    val match_record :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.recordi -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> RiscvPmpBase.coq_Term -> lVar
      RiscvPmpBase.coq_RecordPat -> coq_Assertion -> coq_Assertion

    val match_union_alt :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.unioni -> RiscvPmpBase.coq_Term -> (Coq_ty.unionk -> (lVar,
      coq_Assertion) RiscvPmpBase.coq_Alternative) -> coq_Assertion

    val exs :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Assertion ->
      coq_Assertion

    val sub_assertion :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Assertion -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> RiscvPmpBase.coq_Sub -> coq_Assertion

    val coq_OccursCheckAssertion :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> coq_Assertion -> coq_Assertion
      option

    val is_pure :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Assertion -> bool

    val interpret :
      bi -> coq_PredicateDef -> (lVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> coq_Assertion -> ((lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env -> __

    module Coq_notations :
     sig
     end
   end

  type coq_SepContract = { sep_contract_logic_variables : (lVar,
                                                          Coq_ty.coq_Ty)
                                                          Binding.coq_Binding
                                                          Coq_ctx.coq_Ctx;
                           sep_contract_localstore : RiscvPmpBase.coq_SStore;
                           sep_contract_precondition : Coq_asn.coq_Assertion;
                           sep_contract_result : lVar;
                           sep_contract_postcondition : Coq_asn.coq_Assertion }

  val sep_contract_logic_variables :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContract -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx

  val sep_contract_localstore :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContract -> RiscvPmpBase.coq_SStore

  val sep_contract_precondition :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContract -> Coq_asn.coq_Assertion

  val sep_contract_result :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContract -> lVar

  val sep_contract_postcondition :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContract -> Coq_asn.coq_Assertion

  type coq_Lemma = { lemma_logic_variables : (lVar, Coq_ty.coq_Ty)
                                             Binding.coq_Binding
                                             Coq_ctx.coq_Ctx;
                     lemma_patterns : RiscvPmpBase.coq_SStore;
                     lemma_precondition : Coq_asn.coq_Assertion;
                     lemma_postcondition : Coq_asn.coq_Assertion }

  val lemma_logic_variables :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Lemma ->
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  val lemma_patterns :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Lemma ->
    RiscvPmpBase.coq_SStore

  val lemma_precondition :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Lemma ->
    Coq_asn.coq_Assertion

  val lemma_postcondition :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Lemma ->
    Coq_asn.coq_Assertion

  val lint_assertion :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_In -> Coq_asn.coq_Assertion -> bool

  val lint_contract :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContract -> bool

  val lint_lemma :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Lemma ->
    bool

  val sep_contract_pun_logvars :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  type coq_SepContractPun = { sep_contract_pun_logic_variables : (lVar,
                                                                 Coq_ty.coq_Ty)
                                                                 Binding.coq_Binding
                                                                 Coq_ctx.coq_Ctx;
                              sep_contract_pun_precondition : Coq_asn.coq_Assertion;
                              sep_contract_pun_result : lVar;
                              sep_contract_pun_postcondition : Coq_asn.coq_Assertion }

  val sep_contract_pun_logic_variables :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContractPun -> (lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding Coq_ctx.coq_Ctx

  val sep_contract_pun_precondition :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContractPun -> Coq_asn.coq_Assertion

  val sep_contract_pun_result :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContractPun -> lVar

  val sep_contract_pun_postcondition :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContractPun -> Coq_asn.coq_Assertion

  val sep_contract_pun_to_sep_contract :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContractPun -> coq_SepContract

  val inst_contract_localstore :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> coq_SepContract -> ((lVar, Coq_ty.coq_Ty)
    Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env -> (pVar,
    Coq_ty.coq_Ty, Coq_ty.coq_Val) namedEnv

  val interpret_contract_precondition :
    bi -> coq_PredicateDef -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> coq_SepContract -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env -> __

  val interpret_contract_postcondition :
    bi -> coq_PredicateDef -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> coq_SepContract -> ((lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding, Coq_ty.coq_Val) Coq_env.coq_Env ->
    Coq_ty.coq_Val -> __

  module GenericSolver :
   sig
    val simplify_bool :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> DList.coq_DList

    val simplify_bool_neg :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> DList.coq_DList

    val simplify_eqb :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
      DList.coq_DList

    val simplify_eq_binop_default_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList

    val simplify_eq_unop_default_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
      RiscvPmpBase.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_binop_and_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList

    val simplify_eq_binop_or_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList

    val simplify_eq_unop_not_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_binop_relop_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_binop_pair_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList) -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList

    val simplify_eq_binop_cons_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList) -> Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_binop_bvapp_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList) -> nat -> nat -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_binop_bvcons_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList) -> nat -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_binop_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList) -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      Coq_bop.coq_BinOp -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
      Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_unop_inl_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList) -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      RiscvPmpBase.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_unop_inr_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList) -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      RiscvPmpBase.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_unop_neg_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList) -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList

    val simplify_eq_unop_signed_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList) -> nat -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList

    val simplify_eq_unop_unsigned_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList) -> nat -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList

    val simplify_eq_unop_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList) -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp
      -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_tuple_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList) -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty,
      RiscvPmpBase.coq_Term) Coq_env.coq_Env -> Coq_ty.coq_Val ->
      DList.coq_DList

    val simplify_eq_union_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList) -> Coq_ty.unioni -> Coq_ty.unionk ->
      RiscvPmpBase.coq_Term -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_record_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList) -> Coq_ty.recordi -> (Coq_ty.recordf, Coq_ty.coq_Ty,
      RiscvPmpBase.coq_Term) namedEnv -> Coq_ty.coq_Val -> DList.coq_DList

    val simplify_eq_val :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> Coq_ty.coq_Val ->
      DList.coq_DList

    val simplify_eq_binop_default :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_bop.coq_BinOp ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
      -> DList.coq_DList

    val simplify_eq_binop_minus :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
      -> DList.coq_DList

    val simplify_eq_binop_times :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
      -> DList.coq_DList

    val simplify_eq_unop_default :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList

    val simplify_eq_binop_plus :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
      DList.coq_DList) -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.coq_Term -> DList.coq_DList

    val simplify_eq_binop_and :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
      -> DList.coq_DList

    val simplify_eq_binop_or :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
      -> DList.coq_DList

    val simplify_eq_binop_pair :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
      DList.coq_DList) -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term
      -> DList.coq_DList

    val simplify_eq_binop_cons :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
      DList.coq_DList) -> Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList

    val simplify_eq_binop_append :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
      DList.coq_DList) -> Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList

    val simplify_eq_binop_bvapp' :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
      DList.coq_DList) -> nat -> nat -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.coq_Term -> nat -> RiscvPmpBase.coq_Term -> DList.coq_DList

    val simplify_eq_binop_bvapp :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
      DList.coq_DList) -> nat -> nat -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList

    val simplify_eq_binop_bvcons' :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
      DList.coq_DList) -> nat -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.coq_Term -> nat -> RiscvPmpBase.coq_Term -> DList.coq_DList

    val simplify_eq_binop_bvcons :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
      DList.coq_DList) -> nat -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList

    val simplify_eq_relop :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList

    val simplify_eq_binop :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
      DList.coq_DList) -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      Coq_bop.coq_BinOp -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.coq_Term -> DList.coq_DList

    val simplify_eq_unop_inl :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
      DList.coq_DList) -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList

    val simplify_eq_unop_inr :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
      DList.coq_DList) -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList

    val simplify_eq_unop_get_slice_int :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList

    val simplify_eq_unop_signed :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
      DList.coq_DList) -> nat -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.coq_Term -> DList.coq_DList

    val simplify_eq_unop :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
      DList.coq_DList) -> Coq_ty.coq_Ty -> Coq_ty.coq_Ty -> Coq_uop.coq_UnOp
      -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList

    val formula_eqs_ctx :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
      DList.coq_DList) -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty,
      RiscvPmpBase.coq_Term) Coq_env.coq_Env -> (Coq_ty.coq_Ty,
      RiscvPmpBase.coq_Term) Coq_env.coq_Env -> DList.coq_DList

    val formula_eqs_nctx :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
      DList.coq_DList) -> ('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> ('a1, Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) namedEnv
      -> ('a1, Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) namedEnv ->
      DList.coq_DList

    val simplify_eq_tuple :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
      DList.coq_DList) -> Coq_ty.coq_Ty Coq_ctx.coq_Ctx -> (Coq_ty.coq_Ty,
      RiscvPmpBase.coq_Term) Coq_env.coq_Env -> RiscvPmpBase.coq_Term ->
      DList.coq_DList

    val simplify_eq_record :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
      DList.coq_DList) -> Coq_ty.recordi -> (Coq_ty.recordf, Coq_ty.coq_Ty,
      RiscvPmpBase.coq_Term) namedEnv -> RiscvPmpBase.coq_Term ->
      DList.coq_DList

    val simplify_eq_union :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
      DList.coq_DList) -> Coq_ty.unioni -> Coq_ty.unionk ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList

    val simplify_eq :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
      DList.coq_DList

    val simplify_relopb :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.coq_Term -> DList.coq_DList

    val peval_formula_le' :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> coq_Formula

    val peval_formula_le :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> coq_Formula

    val peval_formula_lt :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> coq_Formula

    val peval_formula_relop_neg :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.coq_Term -> coq_Formula

    val simplify_le :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList

    val simplify_bvule :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList

    val simplify_bvult :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> nat ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList

    val simplify_lt :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> DList.coq_DList

    val simplify_relop :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> Coq_bop.coq_RelOp -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.coq_Term -> DList.coq_DList

    val smart_and :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_Formula -> coq_Formula

    val coq_PathCondition_to_Formula :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_PathCondition -> coq_Formula

    val coq_PathCondition_to_DList :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_PathCondition -> DList.coq_DList

    val simplify_formula :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> DList.coq_DList

    val simplify_pathcondition :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_PathCondition -> DList.coq_DList

    val occurs_check_lt :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
      Coq_ty.coq_Ty) Binding.coq_Binding -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_In -> Coq_ty.coq_Ty ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term option

    val try_unify_bool :
      coq_World -> RiscvPmpBase.coq_Term -> (coq_World, coq_Tri) sigT option

    val try_unify_eq :
      coq_World -> Coq_ty.coq_Ty -> RiscvPmpBase.coq_Term ->
      RiscvPmpBase.coq_Term -> (coq_World, coq_Tri) sigT option

    val try_unify_formula :
      coq_World -> coq_Formula -> (coq_World, coq_Tri) sigT option

    val unify_formula :
      coq_World -> coq_Formula -> (coq_World, (coq_Tri, coq_PathCondition)
      prod) sigT

    val unify_pathcondition :
      coq_World -> coq_PathCondition -> (coq_World, (coq_Tri,
      coq_PathCondition) prod) sigT

    val formula_eqb_clause_3 :
      ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_Formula -> bool) -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> purePredicate -> (Coq_ty.coq_Ty,
      RiscvPmpBase.coq_Term) Coq_env.coq_Env -> purePredicate -> sumbool ->
      (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) Coq_env.coq_Env -> bool

    val formula_eqb_clause_2 :
      ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_Formula -> bool) -> (lVar, Coq_ty.coq_Ty)
      Binding.coq_Binding Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty ->
      Coq_bop.coq_RelOp -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
      Coq_ty.coq_Ty -> sumbool -> Coq_bop.coq_RelOp -> RiscvPmpBase.coq_Term
      -> RiscvPmpBase.coq_Term -> bool

    val formula_eqb :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_Formula -> bool

    val smart_or :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_Formula -> coq_Formula

    val formula_simplifies :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_Formula -> coq_Formula -> coq_Formula option

    val assumption_formula :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_PathCondition -> coq_Formula -> coq_PathCondition ->
      coq_PathCondition

    val assumption_pathcondition :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_PathCondition -> coq_PathCondition -> coq_PathCondition ->
      coq_PathCondition

    val solver_generic : coq_Solver
   end

  val combined_solver : coq_Solver


  module CPureSpec :
   sig
    module Coq_notations :
     sig
     end
   end


  module CHeapSpec :
   sig
    module Coq_notations :
     sig
     end
   end

  module CStatistics :
   sig
    type coq_PropShape =
    | Coq_psfork of coq_PropShape * coq_PropShape
    | Coq_psquant of coq_PropShape
    | Coq_pspruned
    | Coq_psfinish
    | Coq_psother

    val coq_PropShape_rect :
      (coq_PropShape -> 'a1 -> coq_PropShape -> 'a1 -> 'a1) -> (coq_PropShape
      -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> coq_PropShape -> 'a1

    val coq_PropShape_rec :
      (coq_PropShape -> 'a1 -> coq_PropShape -> 'a1 -> 'a1) -> (coq_PropShape
      -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> coq_PropShape -> 'a1

    val shape_to_stats : coq_PropShape -> stats

    type coq_ShallowStats = stats

    val stats : coq_ShallowStats -> stats

    val stats_true : coq_ShallowStats

    val stats_false : coq_ShallowStats

    val stats_finish : coq_ShallowStats

    val stats_true' : coq_ShallowStats

    val stats_false' : coq_ShallowStats

    val stats_eq : 'a1 -> 'a1 -> coq_ShallowStats

    val stats_zle : z -> z -> coq_ShallowStats

    val stats_and : coq_ShallowStats -> coq_ShallowStats -> coq_ShallowStats

    val stats_or : coq_ShallowStats -> coq_ShallowStats -> coq_ShallowStats

    val stats_impl : coq_ShallowStats -> coq_ShallowStats -> coq_ShallowStats

    val undefined : 'a1

    val stats_forall : ('a1 -> coq_ShallowStats) -> coq_ShallowStats

    val stats_exists : ('a1 -> coq_ShallowStats) -> coq_ShallowStats
   end

  type coq_DebugAsn = { debug_asn_pathcondition : coq_PathCondition;
                        debug_asn_heap : coq_SHeap }

  val debug_asn_pathcondition :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DebugAsn
    -> coq_PathCondition

  val debug_asn_heap :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DebugAsn
    -> coq_SHeap

  val coq_SubstDebugAsn : coq_DebugAsn RiscvPmpBase.coq_Subst

  val coq_SubstSUDebugAsn :
    (RiscvPmpBase.coq_WeakensTo, coq_DebugAsn) RiscvPmpBase.coq_SubstSU

  val coq_SubstLawsDebugAsn : coq_DebugAsn RiscvPmpBase.coq_SubstLaws

  val coq_OccursCheckDebugAsn : coq_DebugAsn RiscvPmpBase.coq_OccursCheck

  type coq_DebugConsumeChunk = { debug_consume_chunk_pathcondition : 
                                 coq_PathCondition;
                                 debug_consume_chunk_heap : coq_SHeap;
                                 debug_consume_chunk_chunk : coq_Chunk }

  val debug_consume_chunk_pathcondition :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugConsumeChunk -> coq_PathCondition

  val debug_consume_chunk_heap :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugConsumeChunk -> coq_SHeap

  val debug_consume_chunk_chunk :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugConsumeChunk -> coq_Chunk

  type coq_EDebugConsumeChunk = { edebug_consume_chunk_pathcondition : 
                                  coq_EFormula list;
                                  edebug_consume_chunk_heap : coq_EChunk list;
                                  edebug_consume_chunk_chunk : coq_EChunk }

  val edebug_consume_chunk_pathcondition :
    coq_EDebugConsumeChunk -> coq_EFormula list

  val edebug_consume_chunk_heap : coq_EDebugConsumeChunk -> coq_EChunk list

  val edebug_consume_chunk_chunk : coq_EDebugConsumeChunk -> coq_EChunk

  val coq_Erase_DebugConsumeChunk :
    (coq_DebugConsumeChunk, coq_EDebugConsumeChunk) RiscvPmpBase.coq_Erase

  val coq_SubstDebugConsumeChunk :
    coq_DebugConsumeChunk RiscvPmpBase.coq_Subst

  val coq_SubstSUDebugConsumeChunk :
    'a1 RiscvPmpBase.coq_SubstUniv -> ('a1, coq_DebugConsumeChunk)
    RiscvPmpBase.coq_SubstSU

  val coq_SubstLawsDebugConsumeChunk :
    coq_DebugConsumeChunk RiscvPmpBase.coq_SubstLaws

  val coq_OccursCheckDebugConsumeChunk :
    coq_DebugConsumeChunk RiscvPmpBase.coq_OccursCheck

  type coq_DebugReadRegister = { debug_read_register_pathcondition : 
                                 coq_PathCondition;
                                 debug_read_register_heap : coq_SHeap;
                                 debug_read_register_type : Coq_ty.coq_Ty;
                                 debug_read_register_register : RiscvPmpBase.coq_Reg }

  val debug_read_register_pathcondition :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugReadRegister -> coq_PathCondition

  val debug_read_register_heap :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugReadRegister -> coq_SHeap

  val debug_read_register_type :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugReadRegister -> Coq_ty.coq_Ty

  val debug_read_register_register :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugReadRegister -> RiscvPmpBase.coq_Reg

  type coq_EDebugReadRegister = { edebug_read_register_pathcondition : 
                                  coq_EFormula list;
                                  edebug_read_register_heap : coq_EChunk list;
                                  edebug_read_register_type : Coq_ty.coq_Ty;
                                  edebug_read_register_register : RiscvPmpBase.coq_Reg }

  val edebug_read_register_pathcondition :
    coq_EDebugReadRegister -> coq_EFormula list

  val edebug_read_register_heap : coq_EDebugReadRegister -> coq_EChunk list

  val edebug_read_register_type : coq_EDebugReadRegister -> Coq_ty.coq_Ty

  val edebug_read_register_register :
    coq_EDebugReadRegister -> RiscvPmpBase.coq_Reg

  val coq_EraseDebugReadRegister :
    (coq_DebugReadRegister, coq_EDebugReadRegister) RiscvPmpBase.coq_Erase

  val coq_SubstDebugReadRegister :
    coq_DebugReadRegister RiscvPmpBase.coq_Subst

  val coq_SubstSUDebugReadRegister :
    'a1 RiscvPmpBase.coq_SubstUniv -> ('a1, coq_DebugReadRegister)
    RiscvPmpBase.coq_SubstSU

  val coq_SubstLawsDebugReadRegister :
    coq_DebugReadRegister RiscvPmpBase.coq_SubstLaws

  val coq_OccursCheckDebugReadRegister :
    coq_DebugReadRegister RiscvPmpBase.coq_OccursCheck

  type coq_DebugWriteRegister = { debug_write_register_pathcondition : 
                                  coq_PathCondition;
                                  debug_write_register_heap : coq_SHeap;
                                  debug_write_register_type : Coq_ty.coq_Ty;
                                  debug_write_register_register : RiscvPmpBase.coq_Reg;
                                  debug_write_register_value : RiscvPmpBase.coq_Term }

  val debug_write_register_pathcondition :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugWriteRegister -> coq_PathCondition

  val debug_write_register_heap :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugWriteRegister -> coq_SHeap

  val debug_write_register_type :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugWriteRegister -> Coq_ty.coq_Ty

  val debug_write_register_register :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugWriteRegister -> RiscvPmpBase.coq_Reg

  val debug_write_register_value :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugWriteRegister -> RiscvPmpBase.coq_Term

  type coq_EDebugWriteRegister = { edebug_write_register_pathcondition : 
                                   coq_EFormula list;
                                   edebug_write_register_heap : coq_EChunk
                                                                list;
                                   edebug_write_register_type : Coq_ty.coq_Ty;
                                   edebug_write_register_register : RiscvPmpBase.coq_Reg;
                                   edebug_write_register_value : RiscvPmpBase.coq_ETerm }

  val edebug_write_register_pathcondition :
    coq_EDebugWriteRegister -> coq_EFormula list

  val edebug_write_register_heap : coq_EDebugWriteRegister -> coq_EChunk list

  val edebug_write_register_type : coq_EDebugWriteRegister -> Coq_ty.coq_Ty

  val edebug_write_register_register :
    coq_EDebugWriteRegister -> RiscvPmpBase.coq_Reg

  val edebug_write_register_value :
    coq_EDebugWriteRegister -> RiscvPmpBase.coq_ETerm

  val coq_EraseDebugWriteRegister :
    (coq_DebugWriteRegister, coq_EDebugWriteRegister) RiscvPmpBase.coq_Erase

  val coq_SubstDebugWriteRegister :
    coq_DebugWriteRegister RiscvPmpBase.coq_Subst

  val coq_SubstSUDebugWriteRegister :
    'a1 RiscvPmpBase.coq_SubstUniv -> ('a1, coq_DebugWriteRegister)
    RiscvPmpBase.coq_SubstSU

  val coq_SubstLawsDebugWriteRegister :
    coq_DebugWriteRegister RiscvPmpBase.coq_SubstLaws

  val coq_OccursCheckDebugWriteRegister :
    coq_DebugWriteRegister RiscvPmpBase.coq_OccursCheck

  type coq_DebugString = { debug_string_pathcondition : coq_PathCondition;
                           debug_string_message : string }

  val debug_string_pathcondition :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugString -> coq_PathCondition

  val debug_string_message :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugString -> string

  type coq_EDebugString = { edebug_string_pathcondition : coq_EFormula list;
                            edebug_string_message : string }

  val edebug_string_pathcondition : coq_EDebugString -> coq_EFormula list

  val edebug_string_message : coq_EDebugString -> string

  val coq_EraseDebugString :
    (coq_DebugString, coq_EDebugString) RiscvPmpBase.coq_Erase

  val coq_SubstDebugString : coq_DebugString RiscvPmpBase.coq_Subst

  val coq_SubstSUDebugString :
    (RiscvPmpBase.coq_WeakensTo, coq_DebugString) RiscvPmpBase.coq_SubstSU

  val coq_SubstLawsDebugString : coq_DebugString RiscvPmpBase.coq_SubstLaws

  val coq_OccursCheckDebugString :
    coq_DebugString RiscvPmpBase.coq_OccursCheck

  type coq_DebugAssertFormula = { debug_assert_formula_pathcondition : 
                                  coq_PathCondition;
                                  debug_assert_formula_heap : coq_SHeap;
                                  debug_assert_formula_formula : coq_Formula }

  val debug_assert_formula_pathcondition :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugAssertFormula -> coq_PathCondition

  val debug_assert_formula_heap :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugAssertFormula -> coq_SHeap

  val debug_assert_formula_formula :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugAssertFormula -> coq_Formula

  val coq_SubstDebugAssertFormula :
    coq_DebugAssertFormula RiscvPmpBase.coq_Subst

  val coq_SubstSUDebugAssertFormula :
    (RiscvPmpBase.coq_WeakensTo, coq_DebugAssertFormula)
    RiscvPmpBase.coq_SubstSU

  val coq_SubstLawsDebugAssertFormula :
    coq_DebugAssertFormula RiscvPmpBase.coq_SubstLaws

  val coq_OccursCheckDebugAssertFormula :
    coq_DebugAssertFormula RiscvPmpBase.coq_OccursCheck

  type 'a coq_SPureSpec =
    (('a, SymProp.coq_SymProp) coq_Impl coq_Box, SymProp.coq_SymProp) coq_Impl

  module SPureSpec :
   sig
    val run :
      (RiscvPmpBase.coq_Unit coq_SPureSpec, SymProp.coq_SymProp) coq_Impl
      coq_Valid

    val pure : ('a1, 'a1 coq_SPureSpec) coq_Impl coq_Valid

    val bind :
      ('a1 coq_SPureSpec, (('a1, 'a2 coq_SPureSpec) coq_Impl coq_Box, 'a2
      coq_SPureSpec) coq_Impl) coq_Impl coq_Valid

    module Coq_notations :
     sig
     end

    val block : 'a1 coq_SPureSpec coq_Valid

    val error :
      (RiscvPmpBase.Coq_amsg.coq_AMessage, 'a1 coq_SPureSpec) coq_Impl
      coq_Valid

    val angelic :
      lVar option -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term coq_SPureSpec)
      coq_Forall coq_Valid

    val demonic :
      lVar option -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term coq_SPureSpec)
      coq_Forall coq_Valid

    val angelic_ctx :
      ('a1 -> lVar) -> (('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx, ('a1, Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) namedEnv
      coq_SPureSpec) coq_Forall coq_Valid

    val demonic_ctx :
      ('a1 -> lVar) -> (('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx, ('a1, Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) namedEnv
      coq_SPureSpec) coq_Forall coq_Valid

    val assert_pathcondition :
      (RiscvPmpBase.Coq_amsg.coq_AMessage, (coq_PathCondition,
      RiscvPmpBase.coq_Unit coq_SPureSpec) coq_Impl) coq_Impl coq_Valid

    val assume_pathcondition :
      (coq_PathCondition, RiscvPmpBase.coq_Unit coq_SPureSpec) coq_Impl
      coq_Valid

    val assert_formula :
      (RiscvPmpBase.Coq_amsg.coq_AMessage, (coq_Formula,
      RiscvPmpBase.coq_Unit coq_SPureSpec) coq_Impl) coq_Impl coq_Valid

    val assume_formula :
      (coq_Formula, RiscvPmpBase.coq_Unit coq_SPureSpec) coq_Impl coq_Valid

    val angelic_binary :
      ('a1 coq_SPureSpec, ('a1 coq_SPureSpec, 'a1 coq_SPureSpec) coq_Impl)
      coq_Impl coq_Valid

    val demonic_binary :
      ('a1 coq_SPureSpec, ('a1 coq_SPureSpec, 'a1 coq_SPureSpec) coq_Impl)
      coq_Impl coq_Valid

    val angelic_list' :
      ('a1, ('a1 list, 'a1 coq_SPureSpec) coq_Impl) coq_Impl coq_Valid

    val angelic_list :
      (RiscvPmpBase.Coq_amsg.coq_AMessage, ('a1 list, 'a1 coq_SPureSpec)
      coq_Impl) coq_Impl coq_Valid

    val demonic_list' :
      ('a1, ('a1 list, 'a1 coq_SPureSpec) coq_Impl) coq_Impl coq_Valid

    val demonic_list : ('a1 list, 'a1 coq_SPureSpec) coq_Impl coq_Valid

    val angelic_finite :
      ('a1, 'a1) relDecision -> 'a1 finite ->
      (RiscvPmpBase.Coq_amsg.coq_AMessage, 'a1 RiscvPmpBase.coq_Const
      coq_SPureSpec) coq_Impl coq_Valid

    val demonic_finite :
      ('a1, 'a1) relDecision -> 'a1 finite -> 'a1 RiscvPmpBase.coq_Const
      coq_SPureSpec coq_Valid

    val angelic_pattern_match' :
      ('a1 -> lVar) -> Coq_ty.coq_Ty -> 'a1 RiscvPmpBase.coq_Pattern ->
      (RiscvPmpBase.Coq_amsg.coq_AMessage, (RiscvPmpBase.coq_Term, 'a1
      RiscvPmpBase.coq_SMatchResult coq_SPureSpec) coq_Impl) coq_Impl
      coq_Valid

    val angelic_pattern_match :
      ('a1 -> lVar) -> Coq_ty.coq_Ty -> 'a1 RiscvPmpBase.coq_Pattern ->
      (RiscvPmpBase.Coq_amsg.coq_AMessage, (RiscvPmpBase.coq_Term, 'a1
      RiscvPmpBase.coq_SMatchResult coq_SPureSpec) coq_Impl) coq_Impl
      coq_Valid

    val demonic_pattern_match' :
      ('a1 -> lVar) -> Coq_ty.coq_Ty -> 'a1 RiscvPmpBase.coq_Pattern ->
      (RiscvPmpBase.coq_Term, 'a1 RiscvPmpBase.coq_SMatchResult
      coq_SPureSpec) coq_Impl coq_Valid

    val demonic_pattern_match :
      ('a1 -> lVar) -> Coq_ty.coq_Ty -> 'a1 RiscvPmpBase.coq_Pattern ->
      (RiscvPmpBase.coq_Term, 'a1 RiscvPmpBase.coq_SMatchResult
      coq_SPureSpec) coq_Impl coq_Valid

    val new_pattern_match_regular :
      ('a1 -> lVar) -> Coq_ty.coq_Ty -> 'a1 RiscvPmpBase.coq_Pattern ->
      (RiscvPmpBase.coq_Term, 'a1 RiscvPmpBase.coq_SMatchResult
      coq_SPureSpec) coq_Impl coq_Valid

    val new_pattern_match_var :
      ('a1 -> lVar) -> Coq_ty.coq_Ty -> lVar -> 'a1 RiscvPmpBase.coq_Pattern
      -> ((lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_In, 'a1
      RiscvPmpBase.coq_SMatchResult coq_SPureSpec) coq_Impl coq_Valid

    val new_pattern_match' :
      ('a1 -> lVar) -> Coq_ty.coq_Ty -> 'a1 RiscvPmpBase.coq_Pattern ->
      (RiscvPmpBase.coq_Term, 'a1 RiscvPmpBase.coq_SMatchResult
      coq_SPureSpec) coq_Impl coq_Valid

    val new_pattern_match :
      ('a1 -> lVar) -> Coq_ty.coq_Ty -> 'a1 RiscvPmpBase.coq_Pattern ->
      (RiscvPmpBase.coq_Term, 'a1 RiscvPmpBase.coq_SMatchResult
      coq_SPureSpec) coq_Impl coq_Valid

    val debug :
      (RiscvPmpBase.Coq_amsg.coq_AMessage, ('a1 coq_SPureSpec, 'a1
      coq_SPureSpec) coq_Impl) coq_Impl coq_Valid

    val assert_eq_env :
      (Coq_ty.coq_Ty Coq_ctx.coq_Ctx, (RiscvPmpBase.Coq_amsg.coq_AMessage,
      ((Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) Coq_env.coq_Env,
      ((Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) Coq_env.coq_Env,
      RiscvPmpBase.coq_Unit coq_SPureSpec) coq_Impl) coq_Impl) coq_Impl)
      coq_Forall coq_Valid

    val assert_eq_nenv :
      (('a1, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx,
      (RiscvPmpBase.Coq_amsg.coq_AMessage, (('a1, Coq_ty.coq_Ty,
      RiscvPmpBase.coq_Term) namedEnv, (('a1, Coq_ty.coq_Ty,
      RiscvPmpBase.coq_Term) namedEnv, RiscvPmpBase.coq_Unit coq_SPureSpec)
      coq_Impl) coq_Impl) coq_Impl) coq_Forall coq_Valid

    val assert_eq_chunk :
      (RiscvPmpBase.Coq_amsg.coq_AMessage, (coq_Chunk, (coq_Chunk,
      RiscvPmpBase.coq_Unit coq_SPureSpec coq_Box) coq_Impl) coq_Impl)
      coq_Impl coq_Valid

    val replay_aux :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      SymProp.coq_SymProp -> (RiscvPmpBase.coq_Sub, RiscvPmpBase.coq_Unit
      coq_SPureSpec) coq_Impl coq_Valid

    val replay : (SymProp.coq_SymProp, SymProp.coq_SymProp) coq_Impl coq_Valid

    val produce_chunk :
      (coq_Chunk, (coq_SHeap, coq_SHeap coq_SPureSpec) coq_Impl) coq_Impl
      coq_Valid

    val consume_chunk :
      (coq_Chunk, (coq_SHeap, coq_SHeap coq_SPureSpec) coq_Impl) coq_Impl
      coq_Valid

    val consume_chunk_angelic :
      (coq_Chunk, (coq_SHeap, coq_SHeap coq_SPureSpec) coq_Impl) coq_Impl
      coq_Valid

    val read_register :
      Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg -> (coq_SHeap,
      (RiscvPmpBase.coq_Term, coq_SHeap) RiscvPmpBase.coq_Pair coq_SPureSpec)
      coq_Impl coq_Valid

    val write_register :
      Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg -> (RiscvPmpBase.coq_Term,
      (coq_SHeap, (RiscvPmpBase.coq_Term, coq_SHeap) RiscvPmpBase.coq_Pair
      coq_SPureSpec) coq_Impl) coq_Impl coq_Valid
   end

  type 'a coq_SHeapSpec =
    (('a, (coq_SHeap, SymProp.coq_SymProp) coq_Impl) coq_Impl coq_Box,
    (coq_SHeap, SymProp.coq_SymProp) coq_Impl) coq_Impl

  module SHeapSpec :
   sig
    val run :
      (RiscvPmpBase.coq_Unit coq_SHeapSpec, SymProp.coq_SymProp) coq_Impl
      coq_Valid

    val lift_purespec :
      ('a1 coq_SPureSpec, 'a1 coq_SHeapSpec) coq_Impl coq_Valid

    val pure : ('a1, 'a1 coq_SHeapSpec) coq_Impl coq_Valid

    val bind :
      ('a1 coq_SHeapSpec, (('a1, 'a2 coq_SHeapSpec) coq_Impl coq_Box, 'a2
      coq_SHeapSpec) coq_Impl) coq_Impl coq_Valid

    module Coq_notations :
     sig
     end

    val error :
      ((coq_SHeap, RiscvPmpBase.Coq_amsg.coq_AMessage) coq_Impl, 'a1
      coq_SHeapSpec) coq_Impl coq_Valid

    val angelic :
      lVar option -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term coq_SHeapSpec)
      coq_Forall coq_Valid

    val demonic :
      lVar option -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term coq_SHeapSpec)
      coq_Forall coq_Valid

    val angelic_ctx :
      ('a1 -> lVar) -> (('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx, ('a1, Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) namedEnv
      coq_SHeapSpec) coq_Forall coq_Valid

    val demonic_ctx :
      ('a1 -> lVar) -> (('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx, ('a1, Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) namedEnv
      coq_SHeapSpec) coq_Forall coq_Valid

    val angelic_binary :
      ('a1 coq_SHeapSpec, ('a1 coq_SHeapSpec, 'a1 coq_SHeapSpec) coq_Impl)
      coq_Impl coq_Valid

    val demonic_binary :
      ('a1 coq_SHeapSpec, ('a1 coq_SHeapSpec, 'a1 coq_SHeapSpec) coq_Impl)
      coq_Impl coq_Valid

    val debug :
      ((coq_SHeap, RiscvPmpBase.Coq_amsg.coq_AMessage) coq_Impl, ('a1
      coq_SHeapSpec, 'a1 coq_SHeapSpec) coq_Impl) coq_Impl coq_Valid

    val assert_formula :
      ((coq_SHeap, RiscvPmpBase.Coq_amsg.coq_AMessage) coq_Impl,
      (coq_Formula, RiscvPmpBase.coq_Unit coq_SHeapSpec) coq_Impl) coq_Impl
      coq_Valid

    val assume_formula :
      (coq_Formula, RiscvPmpBase.coq_Unit coq_SHeapSpec) coq_Impl coq_Valid

    val produce_chunk :
      (coq_Chunk, RiscvPmpBase.coq_Unit coq_SHeapSpec) coq_Impl coq_Valid

    val consume_chunk :
      (coq_Chunk, RiscvPmpBase.coq_Unit coq_SHeapSpec) coq_Impl coq_Valid

    val consume_chunk_angelic :
      (coq_Chunk, RiscvPmpBase.coq_Unit coq_SHeapSpec) coq_Impl coq_Valid

    val read_register :
      Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg -> RiscvPmpBase.coq_Term
      coq_SHeapSpec coq_Valid

    val write_register :
      Coq_ty.coq_Ty -> RiscvPmpBase.coq_Reg -> (RiscvPmpBase.coq_Term,
      RiscvPmpBase.coq_Term coq_SHeapSpec) coq_Impl coq_Valid

    val produce :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_asn.coq_Assertion -> (RiscvPmpBase.coq_Sub, RiscvPmpBase.coq_Unit
      coq_SHeapSpec) coq_Impl coq_Valid

    val consume :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_asn.coq_Assertion -> (RiscvPmpBase.coq_Sub, RiscvPmpBase.coq_Unit
      coq_SHeapSpec) coq_Impl coq_Valid

    val call_contract :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> coq_SepContract -> (RiscvPmpBase.coq_SStore,
      RiscvPmpBase.coq_Term coq_SHeapSpec) coq_Impl coq_Valid

    val call_lemma :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Lemma
      -> (RiscvPmpBase.coq_SStore, RiscvPmpBase.coq_Unit coq_SHeapSpec)
      coq_Impl coq_Valid
   end

  val coq_RPureSpec :
    ('a1, 'a2) Coq_logicalrelation.coq_Rel -> ('a1 coq_SPureSpec, 'a2
    coq_CPureSpec) Coq_logicalrelation.coq_Rel

  module PureSpec :
   sig
    val coq_RPureSpec :
      ('a1, 'a2) Coq_logicalrelation.coq_Rel -> ('a1 coq_SPureSpec, 'a2
      coq_CPureSpec) Coq_logicalrelation.coq_Rel
   end

  val coq_RHeapSpec :
    ('a1, 'a2) Coq_logicalrelation.coq_Rel -> ('a1 coq_SHeapSpec, 'a2
    coq_CHeapSpec) Coq_logicalrelation.coq_Rel

  module HeapSpec :
   sig
   end

  val z_term :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> z ->
    RiscvPmpBase.coq_Term

  val sep_contract_logvars :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  val create_localstore :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_SStore

  val asn_and_regs :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    (RiscvPmpBase.coq_Reg -> Coq_asn.coq_Assertion) -> Coq_asn.coq_Assertion

  val asn_regs_ptsto :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_asn.coq_Assertion

  val term_pmp_entries :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_Term

  module Coq_rv_notations :
   sig
   end
 end

module RiscvPmpIrisInstancePredicates :
 sig
  val write_addr : addr
 end

type katamaranLem = RiscvPmpSignature.coq_Lemma

module RiscvPmpSpecification :
 sig
  type coq_SepContractEnv =
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> RiscvPmpProgram.coq_Fun ->
    RiscvPmpSignature.coq_SepContract option

  type coq_SepContractEnvEx =
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> RiscvPmpProgram.coq_FunX ->
    RiscvPmpSignature.coq_SepContract

  type coq_LemmaEnv =
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpProgram.coq_Lem -> RiscvPmpSignature.coq_Lemma

  type coq_SepContractFun = RiscvPmpSignature.coq_SepContract

  type coq_SepContractFunX = RiscvPmpSignature.coq_SepContract

  type coq_SepLemma = katamaranLem

  val instr_exec_contract :
    Coq_ty.coq_Ty -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> RiscvPmpSignature.coq_SepContract

  val sep_contract_execute_RTYPE : coq_SepContractFun

  val sep_contract_execute_MUL : coq_SepContractFun

  val sep_contract_execute_ITYPE : coq_SepContractFun

  val sep_contract_execute_SHIFTIOP : coq_SepContractFun

  val sep_contract_execute_UTYPE : coq_SepContractFun

  val sep_contract_execute_BTYPE : coq_SepContractFun

  val sep_contract_execute_RISCV_JAL : coq_SepContractFun

  val sep_contract_execute_RISCV_JALR : coq_SepContractFun

  val sep_contract_execute_ECALL : coq_SepContractFun

  val sep_contract_execute_EBREAK : coq_SepContractFun

  val sep_contract_execute_MRET : coq_SepContractFun

  val sep_contract_execute_CSR : coq_SepContractFun

  val sep_contract_execute_STORE : coq_SepContractFun

  val sep_contract_execute_LOAD : coq_SepContractFun

  val sep_contract_execute : coq_SepContractFun

  val sep_contract_readCSR : coq_SepContractFun

  val sep_contract_writeCSR : coq_SepContractFun

  val sep_contract_check_CSR : coq_SepContractFun

  val sep_contract_is_CSR_defined : coq_SepContractFun

  val sep_contract_check_CSR_access : coq_SepContractFun

  val sep_contract_privLevel_to_bits : coq_SepContractFun

  val sep_contract_csrAccess : coq_SepContractFun

  val sep_contract_csrPriv : coq_SepContractFun

  val sep_contract_handle_mem_exception : coq_SepContractFun

  val sep_contract_exception_handler : coq_SepContractFun

  val sep_contract_handle_illegal : coq_SepContractFun

  val sep_contract_trap_handler : coq_SepContractFun

  val sep_contract_prepare_trap_vector : coq_SepContractFun

  val sep_contract_tvec_addr : coq_SepContractFun

  val sep_contract_exceptionType_to_bits : coq_SepContractFun

  val sep_contract_exception_delegatee : coq_SepContractFun

  val sep_contract_get_arch_pc : coq_SepContractFun

  val sep_contract_set_next_pc : coq_SepContractFun

  val sep_contract_get_next_pc : coq_SepContractFun

  val sep_contract_tick_pc : coq_SepContractFun

  val sep_contract_to_bits : nat -> coq_SepContractFun

  val sep_contract_rX : coq_SepContractFun

  val sep_contract_wX : coq_SepContractFun

  val sep_contract_step :
    Coq_ty.coq_Ty -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> RiscvPmpSignature.coq_SepContract

  val sep_contract_fetch : coq_SepContractFun

  val sep_contract_init_model : coq_SepContractFun

  val sep_contract_init_sys : coq_SepContractFun

  val sep_contract_init_pmp : coq_SepContractFun

  val sep_contract_within_phys_mem : coq_SepContractFun

  val sep_contract_checked_mem_read : nat -> coq_SepContractFun

  val sep_contract_checked_mem_write : nat -> coq_SepContractFun

  val sep_contract_pmp_mem_read : nat -> coq_SepContractFun

  val sep_contract_pmp_mem_write : nat -> coq_SepContractFun

  val sep_contract_mem_write_value : nat -> coq_SepContractFun

  val sep_contract_mem_read : nat -> coq_SepContractFun

  val sep_contract_pmpCheck : nat -> coq_SepContractFun

  val sep_contract_pmpCheckPerms : coq_SepContractFun

  val sep_contract_pmpCheckRWX : coq_SepContractFun

  val sep_contract_pmpAddrRange : coq_SepContractFun

  val sep_contract_pmpMatchAddr : coq_SepContractFun

  val sep_contract_pmpMatchEntry : coq_SepContractFun

  val sep_contract_pmpLocked : coq_SepContractFun

  val sep_contract_pmpWriteCfg : coq_SepContractFun

  val sep_contract_pmpWriteCfgReg : coq_SepContractFun

  val sep_contract_pmpWriteAddr : coq_SepContractFun

  val coq_CEnv : coq_SepContractEnv

  val sep_contract_read_ram : nat -> coq_SepContractFunX

  val sep_contract_write_ram : nat -> coq_SepContractFunX

  val sep_contract_within_mmio : nat -> coq_SepContractFunX

  val sep_contract_mmio_read : nat -> coq_SepContractFunX

  val sep_contract_mmio_write : nat -> coq_SepContractFunX

  val sep_contract_decode : coq_SepContractFunX

  val sep_contract_externalWorldUpdates : coq_SepContractFunX

  val coq_CEnvEx : coq_SepContractEnvEx

  val lemma_open_gprs : coq_SepLemma

  val lemma_close_gprs : coq_SepLemma

  val lemma_open_ptsto_instr : coq_SepLemma

  val lemma_close_ptsto_instr : coq_SepLemma

  val lemma_open_pmp_entries : coq_SepLemma

  val lemma_close_pmp_entries : coq_SepLemma

  val lemma_extract_pmp_ptsto : nat -> coq_SepLemma

  val lemma_return_pmp_ptsto : nat -> coq_SepLemma

  val lemma_close_mmio_write : Coq_bv.bv -> wordWidth -> coq_SepLemma

  val coq_LEnv : coq_LemmaEnv
 end

module RiscvPmpExecutor :
 sig
  type coq_DebugCall = { debug_call_function_parameters : (pVar,
                                                          Coq_ty.coq_Ty)
                                                          Binding.coq_Binding
                                                          Coq_ctx.coq_Ctx;
                         debug_call_function_result_type : Coq_ty.coq_Ty;
                         debug_call_function_name : RiscvPmpProgram.coq_Fun;
                         debug_call_function_contract : RiscvPmpSignature.coq_SepContract
                                                        option;
                         debug_call_function_arguments : RiscvPmpBase.coq_SStore;
                         debug_call_pathcondition : RiscvPmpSignature.coq_PathCondition;
                         debug_call_heap : RiscvPmpSignature.coq_SHeap }

  val debug_call_function_parameters :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCall -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  val debug_call_function_result_type :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCall -> Coq_ty.coq_Ty

  val debug_call_function_name :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCall -> RiscvPmpProgram.coq_Fun

  val debug_call_function_contract :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCall -> RiscvPmpSignature.coq_SepContract option

  val debug_call_function_arguments :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCall -> RiscvPmpBase.coq_SStore

  val debug_call_pathcondition :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCall -> RiscvPmpSignature.coq_PathCondition

  val debug_call_heap :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCall -> RiscvPmpSignature.coq_SHeap

  type coq_EDebugCall = { edebug_call_function_parameters : (pVar,
                                                            Coq_ty.coq_Ty)
                                                            Binding.coq_Binding
                                                            Coq_ctx.coq_Ctx;
                          edebug_call_function_result_type : Coq_ty.coq_Ty;
                          edebug_call_function_name : RiscvPmpProgram.coq_Fun;
                          edebug_call_function_contract : RiscvPmpSignature.coq_SepContract
                                                          option;
                          edebug_call_function_arguments : (pVar,
                                                           Coq_ty.coq_Ty,
                                                           RiscvPmpBase.coq_ETerm)
                                                           namedEnv;
                          edebug_call_pathcondition : RiscvPmpSignature.coq_EFormula
                                                      list;
                          edebug_call_heap : RiscvPmpSignature.coq_EChunk list }

  val edebug_call_function_parameters :
    coq_EDebugCall -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val edebug_call_function_result_type : coq_EDebugCall -> Coq_ty.coq_Ty

  val edebug_call_function_name : coq_EDebugCall -> RiscvPmpProgram.coq_Fun

  val edebug_call_function_contract :
    coq_EDebugCall -> RiscvPmpSignature.coq_SepContract option

  val edebug_call_function_arguments :
    coq_EDebugCall -> (pVar, Coq_ty.coq_Ty, RiscvPmpBase.coq_ETerm) namedEnv

  val edebug_call_pathcondition :
    coq_EDebugCall -> RiscvPmpSignature.coq_EFormula list

  val edebug_call_heap : coq_EDebugCall -> RiscvPmpSignature.coq_EChunk list

  val coq_EraseDebugCall :
    (coq_DebugCall, coq_EDebugCall) RiscvPmpBase.coq_Erase

  type coq_DebugCallLemma = { debug_call_lemma_parameters : (pVar,
                                                            Coq_ty.coq_Ty)
                                                            Binding.coq_Binding
                                                            Coq_ctx.coq_Ctx;
                              debug_call_lemma_name : RiscvPmpProgram.coq_Lem;
                              debug_call_lemma_contract : RiscvPmpSignature.coq_Lemma;
                              debug_call_lemma_arguments : RiscvPmpBase.coq_SStore;
                              debug_call_lemma_pathcondition : RiscvPmpSignature.coq_PathCondition;
                              debug_call_lemma_heap : RiscvPmpSignature.coq_SHeap }

  val debug_call_lemma_parameters :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCallLemma -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val debug_call_lemma_name :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCallLemma -> RiscvPmpProgram.coq_Lem

  val debug_call_lemma_contract :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCallLemma -> RiscvPmpSignature.coq_Lemma

  val debug_call_lemma_arguments :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCallLemma -> RiscvPmpBase.coq_SStore

  val debug_call_lemma_pathcondition :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCallLemma -> RiscvPmpSignature.coq_PathCondition

  val debug_call_lemma_heap :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCallLemma -> RiscvPmpSignature.coq_SHeap

  type coq_EDebugCallLemma = { edebug_call_lemma_parameters : (pVar,
                                                              Coq_ty.coq_Ty)
                                                              Binding.coq_Binding
                                                              Coq_ctx.coq_Ctx;
                               edebug_call_lemma_name : RiscvPmpProgram.coq_Lem;
                               edebug_call_lemma_contract : RiscvPmpSignature.coq_Lemma;
                               edebug_call_lemma_arguments : (pVar,
                                                             Coq_ty.coq_Ty,
                                                             RiscvPmpBase.coq_ETerm)
                                                             namedEnv;
                               edebug_call_lemma_pathcondition : RiscvPmpSignature.coq_EFormula
                                                                 list;
                               edebug_call_lemma_heap : RiscvPmpSignature.coq_EChunk
                                                        list }

  val edebug_call_lemma_parameters :
    coq_EDebugCallLemma -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val edebug_call_lemma_name : coq_EDebugCallLemma -> RiscvPmpProgram.coq_Lem

  val edebug_call_lemma_contract :
    coq_EDebugCallLemma -> RiscvPmpSignature.coq_Lemma

  val edebug_call_lemma_arguments :
    coq_EDebugCallLemma -> (pVar, Coq_ty.coq_Ty, RiscvPmpBase.coq_ETerm)
    namedEnv

  val edebug_call_lemma_pathcondition :
    coq_EDebugCallLemma -> RiscvPmpSignature.coq_EFormula list

  val edebug_call_lemma_heap :
    coq_EDebugCallLemma -> RiscvPmpSignature.coq_EChunk list

  val coq_EraseDebugCallLemma :
    (coq_DebugCallLemma, coq_EDebugCallLemma) RiscvPmpBase.coq_Erase

  val coq_SubstDebugCallLemma : coq_DebugCallLemma RiscvPmpBase.coq_Subst

  val coq_SubstSUDebugCallLemma :
    'a1 RiscvPmpBase.coq_SubstUniv -> ('a1, coq_DebugCallLemma)
    RiscvPmpBase.coq_SubstSU

  val coq_SubstLawsDebugCallLemma :
    coq_DebugCallLemma RiscvPmpBase.coq_SubstLaws

  val coq_OccursCheckDebugCallLemma :
    coq_DebugCallLemma RiscvPmpBase.coq_OccursCheck

  val coq_GenOccursCheckDebugCallLemma :
    (RiscvPmpBase.coq_WeakensTo, coq_DebugCallLemma)
    RiscvPmpBase.coq_GenOccursCheck

  val coq_SubstDebugCall : coq_DebugCall RiscvPmpBase.coq_Subst

  val coq_SubstSUDebugCall :
    'a1 RiscvPmpBase.coq_SubstUniv -> ('a1, coq_DebugCall)
    RiscvPmpBase.coq_SubstSU

  val coq_SubstLawsDebugCall : coq_DebugCall RiscvPmpBase.coq_SubstLaws

  val coq_OccursCheckDebugCall : coq_DebugCall RiscvPmpBase.coq_OccursCheck

  val coq_GenOccursCheckDebugCall :
    (RiscvPmpBase.coq_WeakensTo, coq_DebugCall)
    RiscvPmpBase.coq_GenOccursCheck

  type coq_DebugStm = { debug_stm_program_context : (pVar, Coq_ty.coq_Ty)
                                                    Binding.coq_Binding
                                                    Coq_ctx.coq_Ctx;
                        debug_stm_statement_type : Coq_ty.coq_Ty;
                        debug_stm_statement : RiscvPmpProgram.coq_Stm;
                        debug_stm_pathcondition : RiscvPmpSignature.coq_PathCondition;
                        debug_stm_localstore : RiscvPmpBase.coq_SStore;
                        debug_stm_heap : RiscvPmpSignature.coq_SHeap }

  val debug_stm_program_context :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DebugStm
    -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  val debug_stm_statement_type :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DebugStm
    -> Coq_ty.coq_Ty

  val debug_stm_statement :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DebugStm
    -> RiscvPmpProgram.coq_Stm

  val debug_stm_pathcondition :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DebugStm
    -> RiscvPmpSignature.coq_PathCondition

  val debug_stm_localstore :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DebugStm
    -> RiscvPmpBase.coq_SStore

  val debug_stm_heap :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DebugStm
    -> RiscvPmpSignature.coq_SHeap

  type coq_EDebugStm = { edebug_stm_program_context : (pVar, Coq_ty.coq_Ty)
                                                      Binding.coq_Binding
                                                      Coq_ctx.coq_Ctx;
                         edebug_stm_statement_type : Coq_ty.coq_Ty;
                         edebug_stm_statement : RiscvPmpProgram.coq_Stm;
                         edebug_stm_pathcondition : RiscvPmpSignature.coq_EFormula
                                                    list;
                         edebug_stm_localstore : (pVar, Coq_ty.coq_Ty,
                                                 RiscvPmpBase.coq_ETerm)
                                                 namedEnv;
                         edebug_stm_heap : RiscvPmpSignature.coq_EChunk list }

  val edebug_stm_program_context :
    coq_EDebugStm -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  val edebug_stm_statement_type : coq_EDebugStm -> Coq_ty.coq_Ty

  val edebug_stm_statement : coq_EDebugStm -> RiscvPmpProgram.coq_Stm

  val edebug_stm_pathcondition :
    coq_EDebugStm -> RiscvPmpSignature.coq_EFormula list

  val edebug_stm_localstore :
    coq_EDebugStm -> (pVar, Coq_ty.coq_Ty, RiscvPmpBase.coq_ETerm) namedEnv

  val edebug_stm_heap : coq_EDebugStm -> RiscvPmpSignature.coq_EChunk list

  val coq_EraseDebugStm : (coq_DebugStm, coq_EDebugStm) RiscvPmpBase.coq_Erase

  val coq_SubstDebugStm : coq_DebugStm RiscvPmpBase.coq_Subst

  val coq_SubstSUDebugStm :
    'a1 RiscvPmpBase.coq_SubstUniv -> ('a1, coq_DebugStm)
    RiscvPmpBase.coq_SubstSU

  val coq_SubstLawsDebugStm : coq_DebugStm RiscvPmpBase.coq_SubstLaws

  val coq_OccursCheckDebugStm : coq_DebugStm RiscvPmpBase.coq_OccursCheck

  val coq_GenOccursCheckDebugStm :
    (RiscvPmpBase.coq_WeakensTo, coq_DebugStm) RiscvPmpBase.coq_GenOccursCheck

  type coq_ErrorNoFuel = { error_no_fuel_call_parameter_types : (pVar,
                                                                Coq_ty.coq_Ty)
                                                                Binding.coq_Binding
                                                                Coq_ctx.coq_Ctx;
                           error_no_fuel_call_return_type : Coq_ty.coq_Ty;
                           error_no_fuel_call_function : RiscvPmpProgram.coq_Fun;
                           error_no_fuel_call_arguments : RiscvPmpBase.coq_SStore;
                           error_no_fuel_pathcondition : RiscvPmpSignature.coq_PathCondition;
                           error_no_fuel_heap : RiscvPmpSignature.coq_SHeap }

  val error_no_fuel_call_parameter_types :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_ErrorNoFuel -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val error_no_fuel_call_return_type :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_ErrorNoFuel -> Coq_ty.coq_Ty

  val error_no_fuel_call_function :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_ErrorNoFuel -> RiscvPmpProgram.coq_Fun

  val error_no_fuel_call_arguments :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_ErrorNoFuel -> RiscvPmpBase.coq_SStore

  val error_no_fuel_pathcondition :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_ErrorNoFuel -> RiscvPmpSignature.coq_PathCondition

  val error_no_fuel_heap :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_ErrorNoFuel -> RiscvPmpSignature.coq_SHeap

  type coq_EErrorNoFuel = { eerror_no_fuel_call_parameter_types : (pVar,
                                                                  Coq_ty.coq_Ty)
                                                                  Binding.coq_Binding
                                                                  Coq_ctx.coq_Ctx;
                            eerror_no_fuel_call_return_type : Coq_ty.coq_Ty;
                            eerror_no_fuel_call_function : RiscvPmpProgram.coq_Fun;
                            eerror_no_fuel_call_arguments : (pVar,
                                                            Coq_ty.coq_Ty,
                                                            RiscvPmpBase.coq_ETerm)
                                                            namedEnv;
                            eerror_no_fuel_pathcondition : RiscvPmpSignature.coq_EFormula
                                                           list;
                            eerror_no_fuel_heap : RiscvPmpSignature.coq_EChunk
                                                  list }

  val eerror_no_fuel_call_parameter_types :
    coq_EErrorNoFuel -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val eerror_no_fuel_call_return_type : coq_EErrorNoFuel -> Coq_ty.coq_Ty

  val eerror_no_fuel_call_function :
    coq_EErrorNoFuel -> RiscvPmpProgram.coq_Fun

  val eerror_no_fuel_call_arguments :
    coq_EErrorNoFuel -> (pVar, Coq_ty.coq_Ty, RiscvPmpBase.coq_ETerm) namedEnv

  val eerror_no_fuel_pathcondition :
    coq_EErrorNoFuel -> RiscvPmpSignature.coq_EFormula list

  val eerror_no_fuel_heap :
    coq_EErrorNoFuel -> RiscvPmpSignature.coq_EChunk list

  val coq_EraseErrorNoFuel :
    (coq_ErrorNoFuel, coq_EErrorNoFuel) RiscvPmpBase.coq_Erase

  val coq_SubstErrorNoFuel : coq_ErrorNoFuel RiscvPmpBase.coq_Subst

  val coq_SubstSUErrorNoFuel :
    'a1 RiscvPmpBase.coq_SubstUniv -> ('a1, coq_ErrorNoFuel)
    RiscvPmpBase.coq_SubstSU

  val coq_SubstLawsErrorNoFuel : coq_ErrorNoFuel RiscvPmpBase.coq_SubstLaws

  val coq_OccursCheckErrorNoFuel :
    coq_ErrorNoFuel RiscvPmpBase.coq_OccursCheck

  val coq_GenOccursCheckErrorNoFuel :
    (RiscvPmpBase.coq_WeakensTo, coq_ErrorNoFuel)
    RiscvPmpBase.coq_GenOccursCheck

  val coq_VerificationCondition_rect :
    RiscvPmpSignature.SymProp.coq_SymProp -> (__ -> 'a1) -> 'a1

  val coq_VerificationCondition_rec :
    RiscvPmpSignature.SymProp.coq_SymProp -> (__ -> 'a1) -> 'a1

  val coq_VerificationConditionWithErasure_rect :
    RiscvPmpSignature.Erasure.coq_ESymProp -> (__ -> 'a1) -> 'a1

  val coq_VerificationConditionWithErasure_rec :
    RiscvPmpSignature.Erasure.coq_ESymProp -> (__ -> 'a1) -> 'a1

  type coq_Config = { config_debug_function : ((pVar, Coq_ty.coq_Ty)
                                              Binding.coq_Binding
                                              Coq_ctx.coq_Ctx ->
                                              Coq_ty.coq_Ty ->
                                              RiscvPmpProgram.coq_Fun -> bool);
                      config_debug_lemma : ((pVar, Coq_ty.coq_Ty)
                                           Binding.coq_Binding
                                           Coq_ctx.coq_Ctx ->
                                           RiscvPmpProgram.coq_Lem -> bool) }

  val config_debug_function :
    coq_Config -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> Coq_ty.coq_Ty -> RiscvPmpProgram.coq_Fun -> bool

  val config_debug_lemma :
    coq_Config -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> RiscvPmpProgram.coq_Lem -> bool

  val default_config : coq_Config

  type 'a coq_SStoreSpec =
    (('a, (RiscvPmpBase.coq_SStore, (RiscvPmpSignature.coq_SHeap,
    RiscvPmpSignature.SymProp.coq_SymProp) RiscvPmpSignature.coq_Impl)
    RiscvPmpSignature.coq_Impl) RiscvPmpSignature.coq_Impl
    RiscvPmpSignature.coq_Box, (RiscvPmpBase.coq_SStore,
    (RiscvPmpSignature.coq_SHeap, RiscvPmpSignature.SymProp.coq_SymProp)
    RiscvPmpSignature.coq_Impl) RiscvPmpSignature.coq_Impl)
    RiscvPmpSignature.coq_Impl

  type coq_ExecCall =
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> RiscvPmpProgram.coq_Fun -> (RiscvPmpBase.coq_SStore,
    RiscvPmpBase.coq_Term RiscvPmpSignature.coq_SHeapSpec)
    RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

  type coq_ExecCallForeign =
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> RiscvPmpProgram.coq_FunX -> (RiscvPmpBase.coq_SStore,
    RiscvPmpBase.coq_Term RiscvPmpSignature.coq_SHeapSpec)
    RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

  type coq_ExecLemma =
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpProgram.coq_Lem -> (RiscvPmpBase.coq_SStore,
    RiscvPmpBase.coq_Unit RiscvPmpSignature.coq_SHeapSpec)
    RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

  type coq_ExecFail =
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Val -> RiscvPmpBase.coq_Term coq_SStoreSpec
    RiscvPmpSignature.coq_Valid

  type coq_Exec =
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> RiscvPmpProgram.coq_Stm -> RiscvPmpBase.coq_Term
    coq_SStoreSpec RiscvPmpSignature.coq_Valid

  module SStoreSpec :
   sig
    val evalStoreSpec :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
      coq_SStoreSpec, (RiscvPmpBase.coq_SStore, 'a1
      RiscvPmpSignature.coq_SHeapSpec) RiscvPmpSignature.coq_Impl)
      RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

    val lift_purespec :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
      RiscvPmpSignature.coq_SPureSpec, 'a1 coq_SStoreSpec)
      RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

    val lift_heapspec :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
      RiscvPmpSignature.coq_SHeapSpec, 'a1 coq_SStoreSpec)
      RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

    val pure :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, 'a1
      coq_SStoreSpec) RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

    val bind :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
      coq_SStoreSpec, (('a1, 'a2 coq_SStoreSpec) RiscvPmpSignature.coq_Impl
      RiscvPmpSignature.coq_Box, 'a2 coq_SStoreSpec)
      RiscvPmpSignature.coq_Impl) RiscvPmpSignature.coq_Impl
      RiscvPmpSignature.coq_Valid

    val error :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      ((RiscvPmpBase.coq_SStore, (RiscvPmpSignature.coq_SHeap,
      RiscvPmpBase.Coq_amsg.coq_AMessage) RiscvPmpSignature.coq_Impl)
      RiscvPmpSignature.coq_Impl, 'a1 coq_SStoreSpec)
      RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

    val block :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1
      coq_SStoreSpec RiscvPmpSignature.coq_Valid

    val angelic_binary :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
      coq_SStoreSpec, ('a1 coq_SStoreSpec, 'a1 coq_SStoreSpec)
      RiscvPmpSignature.coq_Impl) RiscvPmpSignature.coq_Impl
      RiscvPmpSignature.coq_Valid

    val demonic_binary :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
      coq_SStoreSpec, ('a1 coq_SStoreSpec, 'a1 coq_SStoreSpec)
      RiscvPmpSignature.coq_Impl) RiscvPmpSignature.coq_Impl
      RiscvPmpSignature.coq_Valid

    val angelic :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar
      option -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term coq_SStoreSpec)
      RiscvPmpSignature.coq_Forall RiscvPmpSignature.coq_Valid

    val demonic :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar
      option -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term coq_SStoreSpec)
      RiscvPmpSignature.coq_Forall RiscvPmpSignature.coq_Valid

    val debug :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      ((RiscvPmpBase.coq_SStore, (RiscvPmpSignature.coq_SHeap,
      RiscvPmpBase.Coq_amsg.coq_AMessage) RiscvPmpSignature.coq_Impl)
      RiscvPmpSignature.coq_Impl, ('a1 coq_SStoreSpec, 'a1 coq_SStoreSpec)
      RiscvPmpSignature.coq_Impl) RiscvPmpSignature.coq_Impl
      RiscvPmpSignature.coq_Valid

    val angelic_ctx :
      ('a1 -> lVar) -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx, ('a1, Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) namedEnv
      coq_SStoreSpec) RiscvPmpSignature.coq_Forall RiscvPmpSignature.coq_Valid

    val demonic_ctx :
      ('a1 -> lVar) -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx, ('a1, Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) namedEnv
      coq_SStoreSpec) RiscvPmpSignature.coq_Forall RiscvPmpSignature.coq_Valid

    module Coq_notations :
     sig
     end

    val demonic_pattern_match :
      ('a1 -> lVar) -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 RiscvPmpBase.coq_Pattern ->
      (RiscvPmpBase.coq_Term, 'a1 RiscvPmpBase.coq_SMatchResult
      coq_SStoreSpec) RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

    val pushpop :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> pVar ->
      Coq_ty.coq_Ty -> (RiscvPmpBase.coq_Term, ('a1 coq_SStoreSpec, 'a1
      coq_SStoreSpec) RiscvPmpSignature.coq_Impl) RiscvPmpSignature.coq_Impl
      RiscvPmpSignature.coq_Valid

    val pushspops :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (RiscvPmpBase.coq_SStore, ('a1 coq_SStoreSpec, 'a1 coq_SStoreSpec)
      RiscvPmpSignature.coq_Impl) RiscvPmpSignature.coq_Impl
      RiscvPmpSignature.coq_Valid

    val get_local :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_SStore coq_SStoreSpec RiscvPmpSignature.coq_Valid

    val put_local :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (RiscvPmpBase.coq_SStore, RiscvPmpBase.coq_Unit coq_SStoreSpec)
      RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

    val eval_exp :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> RiscvPmpBase.coq_Exp -> RiscvPmpBase.coq_Term
      coq_SStoreSpec RiscvPmpSignature.coq_Valid

    val eval_exps :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty, RiscvPmpBase.coq_Exp) namedEnv ->
      RiscvPmpBase.coq_SStore coq_SStoreSpec RiscvPmpSignature.coq_Valid

    val assign :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> pVar ->
      Coq_ty.coq_Ty -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> (RiscvPmpBase.coq_Term, RiscvPmpBase.coq_Unit
      coq_SStoreSpec) RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

    val exec_aux :
      coq_ExecCallForeign -> coq_ExecLemma -> coq_ExecCall -> coq_ExecFail ->
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> RiscvPmpProgram.coq_Stm -> RiscvPmpBase.coq_Term
      coq_SStoreSpec RiscvPmpSignature.coq_Valid
   end

  val exec_contract :
    coq_Exec -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> RiscvPmpSignature.coq_SepContract ->
    RiscvPmpProgram.coq_Stm -> RiscvPmpBase.coq_Unit
    RiscvPmpSignature.coq_SHeapSpec RiscvPmpSignature.coq_Valid

  val exec_call_error_no_fuel : coq_ExecCall

  val sexec_call_foreign : coq_ExecCallForeign

  val debug_lemma :
    coq_Config -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> RiscvPmpProgram.coq_Lem -> (RiscvPmpBase.coq_SStore,
    RiscvPmpBase.coq_Unit RiscvPmpSignature.coq_SHeapSpec)
    RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

  val sexec_lemma : coq_Config -> coq_ExecLemma

  val debug_call :
    coq_Config -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> Coq_ty.coq_Ty -> RiscvPmpProgram.coq_Fun -> (RiscvPmpBase.coq_SStore,
    RiscvPmpBase.coq_Unit RiscvPmpSignature.coq_SHeapSpec)
    RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

  val sexec_fail : coq_ExecFail

  val sexec_call : coq_Config -> nat -> coq_ExecCall

  val sexec : coq_Config -> nat -> coq_Exec

  val vcgen :
    coq_Config -> nat -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> RiscvPmpSignature.coq_SepContract ->
    RiscvPmpProgram.coq_Stm -> RiscvPmpSignature.SymProp.coq_SymProp
    RiscvPmpSignature.coq_Valid

  module Symbolic :
   sig
    val verification_failed_with_error :
      RiscvPmpBase.Coq_amsg.coq_EAMessage -> bool

    val ok' :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpSignature.SymProp.coq_SymProp -> bool

    val ok :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpSignature.SymProp.coq_SymProp -> bool

    val coq_VcGenErasureFuel :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> nat -> RiscvPmpSignature.coq_SepContract ->
      RiscvPmpProgram.coq_Stm -> RiscvPmpSignature.Erasure.coq_ESymProp

    val coq_VcGenErasure :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> RiscvPmpSignature.coq_SepContract ->
      RiscvPmpProgram.coq_Stm -> RiscvPmpSignature.Erasure.coq_ESymProp

    module Statistics :
     sig
      val extend_postcond_with_debug :
        (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> RiscvPmpSignature.coq_SepContract ->
        RiscvPmpSignature.coq_SepContract

      val calc :
        (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> RiscvPmpProgram.coq_Fun -> stats option
     end
   end
 end

module RiscvPmpBlockVerifFailLogic :
 sig
  val fail_rule_pre : bool
 end

module RiscvPmpBlockVerifSpec :
 sig
  type coq_SepContractEnv =
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> RiscvPmpProgram.coq_Fun ->
    RiscvPmpSignature.coq_SepContract option

  type coq_SepContractEnvEx =
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> RiscvPmpProgram.coq_FunX ->
    RiscvPmpSignature.coq_SepContract

  type coq_LemmaEnv =
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpProgram.coq_Lem -> RiscvPmpSignature.coq_Lemma

  val term_eqb :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term

  val z_term :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> z ->
    RiscvPmpBase.coq_Term

  val sep_contract_logvars :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  val create_localstore :
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (lVar,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_SStore

  type coq_SepContractFun = RiscvPmpSignature.coq_SepContract

  type coq_SepContractFunX = RiscvPmpSignature.coq_SepContract

  type coq_SepLemma = RiscvPmpSignature.coq_Lemma

  val asn_exists :
    (string, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (string,
    Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpSignature.Coq_asn.coq_Assertion ->
    RiscvPmpSignature.Coq_asn.coq_Assertion

  val asn_with_reg :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_Term -> (RiscvPmpBase.coq_Reg ->
    RiscvPmpSignature.Coq_asn.coq_Assertion) ->
    RiscvPmpSignature.Coq_asn.coq_Assertion ->
    RiscvPmpSignature.Coq_asn.coq_Assertion

  val asn_reg_ptsto :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
    RiscvPmpSignature.Coq_asn.coq_Assertion

  val sep_contract_rX : RiscvPmpSpecification.coq_SepContractFun

  val sep_contract_wX : RiscvPmpSpecification.coq_SepContractFun

  val sep_contract_fetch_instr : RiscvPmpSpecification.coq_SepContractFun

  val sep_contract_checked_mem_read :
    nat -> RiscvPmpSpecification.coq_SepContractFun

  val sep_contract_checked_mem_write :
    nat -> RiscvPmpSpecification.coq_SepContractFun

  val sep_contract_pmpCheck : nat -> RiscvPmpSpecification.coq_SepContractFun

  val sep_contract_pmp_mem_read :
    nat -> RiscvPmpSpecification.coq_SepContractFun

  val sep_contract_pmp_mem_write :
    nat -> RiscvPmpSpecification.coq_SepContractFun

  val sep_contract_mem_read : nat -> RiscvPmpSpecification.coq_SepContractFun

  val sep_contract_mem_write_value :
    nat -> RiscvPmpSpecification.coq_SepContractFun

  val sep_contract_tick_pc : RiscvPmpSpecification.coq_SepContractFun

  val sep_contract_within_phys_mem : RiscvPmpSpecification.coq_SepContractFun

  val sep_contract_execute_EBREAK : RiscvPmpSpecification.coq_SepContractFun

  val coq_CEnv : RiscvPmpSpecification.coq_SepContractEnv

  val sep_contract_read_ram : nat -> RiscvPmpSpecification.coq_SepContractFunX

  val sep_contract_write_ram :
    nat -> RiscvPmpSpecification.coq_SepContractFunX

  val sep_contract_within_mmio :
    nat -> RiscvPmpSpecification.coq_SepContractFunX

  val sep_contract_mmio_write :
    nat -> RiscvPmpSpecification.coq_SepContractFunX

  val sep_contract_decode : RiscvPmpSpecification.coq_SepContractFunX

  val coq_CEnvEx : RiscvPmpSpecification.coq_SepContractEnvEx

  val lemma_open_gprs : RiscvPmpSpecification.coq_SepLemma

  val lemma_close_gprs : RiscvPmpSpecification.coq_SepLemma

  val lemma_open_ptsto_instr : RiscvPmpSpecification.coq_SepLemma

  val lemma_close_ptsto_instr : RiscvPmpSpecification.coq_SepLemma

  val lemma_extract_pmp_ptsto : nat -> RiscvPmpSpecification.coq_SepLemma

  val lemma_return_pmp_ptsto : nat -> RiscvPmpSpecification.coq_SepLemma

  val map_wordwidth : wordWidth -> nat

  val lemma_close_mmio_write :
    Coq_bv.bv -> wordWidth -> RiscvPmpSpecification.coq_SepLemma

  val coq_LEnv : RiscvPmpSpecification.coq_LemmaEnv
 end

module RiscvPmpBlockVerifExecutor :
 sig
  type coq_DebugCall = { debug_call_function_parameters : (pVar,
                                                          Coq_ty.coq_Ty)
                                                          Binding.coq_Binding
                                                          Coq_ctx.coq_Ctx;
                         debug_call_function_result_type : Coq_ty.coq_Ty;
                         debug_call_function_name : RiscvPmpProgram.coq_Fun;
                         debug_call_function_contract : RiscvPmpSignature.coq_SepContract
                                                        option;
                         debug_call_function_arguments : RiscvPmpBase.coq_SStore;
                         debug_call_pathcondition : RiscvPmpSignature.coq_PathCondition;
                         debug_call_heap : RiscvPmpSignature.coq_SHeap }

  val debug_call_function_parameters :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCall -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  val debug_call_function_result_type :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCall -> Coq_ty.coq_Ty

  val debug_call_function_name :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCall -> RiscvPmpProgram.coq_Fun

  val debug_call_function_contract :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCall -> RiscvPmpSignature.coq_SepContract option

  val debug_call_function_arguments :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCall -> RiscvPmpBase.coq_SStore

  val debug_call_pathcondition :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCall -> RiscvPmpSignature.coq_PathCondition

  val debug_call_heap :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCall -> RiscvPmpSignature.coq_SHeap

  type coq_EDebugCall = { edebug_call_function_parameters : (pVar,
                                                            Coq_ty.coq_Ty)
                                                            Binding.coq_Binding
                                                            Coq_ctx.coq_Ctx;
                          edebug_call_function_result_type : Coq_ty.coq_Ty;
                          edebug_call_function_name : RiscvPmpProgram.coq_Fun;
                          edebug_call_function_contract : RiscvPmpSignature.coq_SepContract
                                                          option;
                          edebug_call_function_arguments : (pVar,
                                                           Coq_ty.coq_Ty,
                                                           RiscvPmpBase.coq_ETerm)
                                                           namedEnv;
                          edebug_call_pathcondition : RiscvPmpSignature.coq_EFormula
                                                      list;
                          edebug_call_heap : RiscvPmpSignature.coq_EChunk list }

  val edebug_call_function_parameters :
    coq_EDebugCall -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val edebug_call_function_result_type : coq_EDebugCall -> Coq_ty.coq_Ty

  val edebug_call_function_name : coq_EDebugCall -> RiscvPmpProgram.coq_Fun

  val edebug_call_function_contract :
    coq_EDebugCall -> RiscvPmpSignature.coq_SepContract option

  val edebug_call_function_arguments :
    coq_EDebugCall -> (pVar, Coq_ty.coq_Ty, RiscvPmpBase.coq_ETerm) namedEnv

  val edebug_call_pathcondition :
    coq_EDebugCall -> RiscvPmpSignature.coq_EFormula list

  val edebug_call_heap : coq_EDebugCall -> RiscvPmpSignature.coq_EChunk list

  val coq_EraseDebugCall :
    (coq_DebugCall, coq_EDebugCall) RiscvPmpBase.coq_Erase

  type coq_DebugCallLemma = { debug_call_lemma_parameters : (pVar,
                                                            Coq_ty.coq_Ty)
                                                            Binding.coq_Binding
                                                            Coq_ctx.coq_Ctx;
                              debug_call_lemma_name : RiscvPmpProgram.coq_Lem;
                              debug_call_lemma_contract : RiscvPmpSignature.coq_Lemma;
                              debug_call_lemma_arguments : RiscvPmpBase.coq_SStore;
                              debug_call_lemma_pathcondition : RiscvPmpSignature.coq_PathCondition;
                              debug_call_lemma_heap : RiscvPmpSignature.coq_SHeap }

  val debug_call_lemma_parameters :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCallLemma -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val debug_call_lemma_name :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCallLemma -> RiscvPmpProgram.coq_Lem

  val debug_call_lemma_contract :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCallLemma -> RiscvPmpSignature.coq_Lemma

  val debug_call_lemma_arguments :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCallLemma -> RiscvPmpBase.coq_SStore

  val debug_call_lemma_pathcondition :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCallLemma -> RiscvPmpSignature.coq_PathCondition

  val debug_call_lemma_heap :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_DebugCallLemma -> RiscvPmpSignature.coq_SHeap

  type coq_EDebugCallLemma = { edebug_call_lemma_parameters : (pVar,
                                                              Coq_ty.coq_Ty)
                                                              Binding.coq_Binding
                                                              Coq_ctx.coq_Ctx;
                               edebug_call_lemma_name : RiscvPmpProgram.coq_Lem;
                               edebug_call_lemma_contract : RiscvPmpSignature.coq_Lemma;
                               edebug_call_lemma_arguments : (pVar,
                                                             Coq_ty.coq_Ty,
                                                             RiscvPmpBase.coq_ETerm)
                                                             namedEnv;
                               edebug_call_lemma_pathcondition : RiscvPmpSignature.coq_EFormula
                                                                 list;
                               edebug_call_lemma_heap : RiscvPmpSignature.coq_EChunk
                                                        list }

  val edebug_call_lemma_parameters :
    coq_EDebugCallLemma -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val edebug_call_lemma_name : coq_EDebugCallLemma -> RiscvPmpProgram.coq_Lem

  val edebug_call_lemma_contract :
    coq_EDebugCallLemma -> RiscvPmpSignature.coq_Lemma

  val edebug_call_lemma_arguments :
    coq_EDebugCallLemma -> (pVar, Coq_ty.coq_Ty, RiscvPmpBase.coq_ETerm)
    namedEnv

  val edebug_call_lemma_pathcondition :
    coq_EDebugCallLemma -> RiscvPmpSignature.coq_EFormula list

  val edebug_call_lemma_heap :
    coq_EDebugCallLemma -> RiscvPmpSignature.coq_EChunk list

  val coq_EraseDebugCallLemma :
    (coq_DebugCallLemma, coq_EDebugCallLemma) RiscvPmpBase.coq_Erase

  val coq_SubstDebugCallLemma : coq_DebugCallLemma RiscvPmpBase.coq_Subst

  val coq_SubstSUDebugCallLemma :
    'a1 RiscvPmpBase.coq_SubstUniv -> ('a1, coq_DebugCallLemma)
    RiscvPmpBase.coq_SubstSU

  val coq_SubstLawsDebugCallLemma :
    coq_DebugCallLemma RiscvPmpBase.coq_SubstLaws

  val coq_OccursCheckDebugCallLemma :
    coq_DebugCallLemma RiscvPmpBase.coq_OccursCheck

  val coq_GenOccursCheckDebugCallLemma :
    (RiscvPmpBase.coq_WeakensTo, coq_DebugCallLemma)
    RiscvPmpBase.coq_GenOccursCheck

  val coq_SubstDebugCall : coq_DebugCall RiscvPmpBase.coq_Subst

  val coq_SubstSUDebugCall :
    'a1 RiscvPmpBase.coq_SubstUniv -> ('a1, coq_DebugCall)
    RiscvPmpBase.coq_SubstSU

  val coq_SubstLawsDebugCall : coq_DebugCall RiscvPmpBase.coq_SubstLaws

  val coq_OccursCheckDebugCall : coq_DebugCall RiscvPmpBase.coq_OccursCheck

  val coq_GenOccursCheckDebugCall :
    (RiscvPmpBase.coq_WeakensTo, coq_DebugCall)
    RiscvPmpBase.coq_GenOccursCheck

  type coq_DebugStm = { debug_stm_program_context : (pVar, Coq_ty.coq_Ty)
                                                    Binding.coq_Binding
                                                    Coq_ctx.coq_Ctx;
                        debug_stm_statement_type : Coq_ty.coq_Ty;
                        debug_stm_statement : RiscvPmpProgram.coq_Stm;
                        debug_stm_pathcondition : RiscvPmpSignature.coq_PathCondition;
                        debug_stm_localstore : RiscvPmpBase.coq_SStore;
                        debug_stm_heap : RiscvPmpSignature.coq_SHeap }

  val debug_stm_program_context :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DebugStm
    -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  val debug_stm_statement_type :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DebugStm
    -> Coq_ty.coq_Ty

  val debug_stm_statement :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DebugStm
    -> RiscvPmpProgram.coq_Stm

  val debug_stm_pathcondition :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DebugStm
    -> RiscvPmpSignature.coq_PathCondition

  val debug_stm_localstore :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DebugStm
    -> RiscvPmpBase.coq_SStore

  val debug_stm_heap :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_DebugStm
    -> RiscvPmpSignature.coq_SHeap

  type coq_EDebugStm = { edebug_stm_program_context : (pVar, Coq_ty.coq_Ty)
                                                      Binding.coq_Binding
                                                      Coq_ctx.coq_Ctx;
                         edebug_stm_statement_type : Coq_ty.coq_Ty;
                         edebug_stm_statement : RiscvPmpProgram.coq_Stm;
                         edebug_stm_pathcondition : RiscvPmpSignature.coq_EFormula
                                                    list;
                         edebug_stm_localstore : (pVar, Coq_ty.coq_Ty,
                                                 RiscvPmpBase.coq_ETerm)
                                                 namedEnv;
                         edebug_stm_heap : RiscvPmpSignature.coq_EChunk list }

  val edebug_stm_program_context :
    coq_EDebugStm -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx

  val edebug_stm_statement_type : coq_EDebugStm -> Coq_ty.coq_Ty

  val edebug_stm_statement : coq_EDebugStm -> RiscvPmpProgram.coq_Stm

  val edebug_stm_pathcondition :
    coq_EDebugStm -> RiscvPmpSignature.coq_EFormula list

  val edebug_stm_localstore :
    coq_EDebugStm -> (pVar, Coq_ty.coq_Ty, RiscvPmpBase.coq_ETerm) namedEnv

  val edebug_stm_heap : coq_EDebugStm -> RiscvPmpSignature.coq_EChunk list

  val coq_EraseDebugStm : (coq_DebugStm, coq_EDebugStm) RiscvPmpBase.coq_Erase

  val coq_SubstDebugStm : coq_DebugStm RiscvPmpBase.coq_Subst

  val coq_SubstSUDebugStm :
    'a1 RiscvPmpBase.coq_SubstUniv -> ('a1, coq_DebugStm)
    RiscvPmpBase.coq_SubstSU

  val coq_SubstLawsDebugStm : coq_DebugStm RiscvPmpBase.coq_SubstLaws

  val coq_OccursCheckDebugStm : coq_DebugStm RiscvPmpBase.coq_OccursCheck

  val coq_GenOccursCheckDebugStm :
    (RiscvPmpBase.coq_WeakensTo, coq_DebugStm) RiscvPmpBase.coq_GenOccursCheck

  type coq_ErrorNoFuel = { error_no_fuel_call_parameter_types : (pVar,
                                                                Coq_ty.coq_Ty)
                                                                Binding.coq_Binding
                                                                Coq_ctx.coq_Ctx;
                           error_no_fuel_call_return_type : Coq_ty.coq_Ty;
                           error_no_fuel_call_function : RiscvPmpProgram.coq_Fun;
                           error_no_fuel_call_arguments : RiscvPmpBase.coq_SStore;
                           error_no_fuel_pathcondition : RiscvPmpSignature.coq_PathCondition;
                           error_no_fuel_heap : RiscvPmpSignature.coq_SHeap }

  val error_no_fuel_call_parameter_types :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_ErrorNoFuel -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val error_no_fuel_call_return_type :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_ErrorNoFuel -> Coq_ty.coq_Ty

  val error_no_fuel_call_function :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_ErrorNoFuel -> RiscvPmpProgram.coq_Fun

  val error_no_fuel_call_arguments :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_ErrorNoFuel -> RiscvPmpBase.coq_SStore

  val error_no_fuel_pathcondition :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_ErrorNoFuel -> RiscvPmpSignature.coq_PathCondition

  val error_no_fuel_heap :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_ErrorNoFuel -> RiscvPmpSignature.coq_SHeap

  type coq_EErrorNoFuel = { eerror_no_fuel_call_parameter_types : (pVar,
                                                                  Coq_ty.coq_Ty)
                                                                  Binding.coq_Binding
                                                                  Coq_ctx.coq_Ctx;
                            eerror_no_fuel_call_return_type : Coq_ty.coq_Ty;
                            eerror_no_fuel_call_function : RiscvPmpProgram.coq_Fun;
                            eerror_no_fuel_call_arguments : (pVar,
                                                            Coq_ty.coq_Ty,
                                                            RiscvPmpBase.coq_ETerm)
                                                            namedEnv;
                            eerror_no_fuel_pathcondition : RiscvPmpSignature.coq_EFormula
                                                           list;
                            eerror_no_fuel_heap : RiscvPmpSignature.coq_EChunk
                                                  list }

  val eerror_no_fuel_call_parameter_types :
    coq_EErrorNoFuel -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx

  val eerror_no_fuel_call_return_type : coq_EErrorNoFuel -> Coq_ty.coq_Ty

  val eerror_no_fuel_call_function :
    coq_EErrorNoFuel -> RiscvPmpProgram.coq_Fun

  val eerror_no_fuel_call_arguments :
    coq_EErrorNoFuel -> (pVar, Coq_ty.coq_Ty, RiscvPmpBase.coq_ETerm) namedEnv

  val eerror_no_fuel_pathcondition :
    coq_EErrorNoFuel -> RiscvPmpSignature.coq_EFormula list

  val eerror_no_fuel_heap :
    coq_EErrorNoFuel -> RiscvPmpSignature.coq_EChunk list

  val coq_EraseErrorNoFuel :
    (coq_ErrorNoFuel, coq_EErrorNoFuel) RiscvPmpBase.coq_Erase

  val coq_SubstErrorNoFuel : coq_ErrorNoFuel RiscvPmpBase.coq_Subst

  val coq_SubstSUErrorNoFuel :
    'a1 RiscvPmpBase.coq_SubstUniv -> ('a1, coq_ErrorNoFuel)
    RiscvPmpBase.coq_SubstSU

  val coq_SubstLawsErrorNoFuel : coq_ErrorNoFuel RiscvPmpBase.coq_SubstLaws

  val coq_OccursCheckErrorNoFuel :
    coq_ErrorNoFuel RiscvPmpBase.coq_OccursCheck

  val coq_GenOccursCheckErrorNoFuel :
    (RiscvPmpBase.coq_WeakensTo, coq_ErrorNoFuel)
    RiscvPmpBase.coq_GenOccursCheck

  val coq_VerificationCondition_rect :
    RiscvPmpSignature.SymProp.coq_SymProp -> (__ -> 'a1) -> 'a1

  val coq_VerificationCondition_rec :
    RiscvPmpSignature.SymProp.coq_SymProp -> (__ -> 'a1) -> 'a1

  val coq_VerificationConditionWithErasure_rect :
    RiscvPmpSignature.Erasure.coq_ESymProp -> (__ -> 'a1) -> 'a1

  val coq_VerificationConditionWithErasure_rec :
    RiscvPmpSignature.Erasure.coq_ESymProp -> (__ -> 'a1) -> 'a1

  type coq_Config = { config_debug_function : ((pVar, Coq_ty.coq_Ty)
                                              Binding.coq_Binding
                                              Coq_ctx.coq_Ctx ->
                                              Coq_ty.coq_Ty ->
                                              RiscvPmpProgram.coq_Fun -> bool);
                      config_debug_lemma : ((pVar, Coq_ty.coq_Ty)
                                           Binding.coq_Binding
                                           Coq_ctx.coq_Ctx ->
                                           RiscvPmpProgram.coq_Lem -> bool) }

  val config_debug_function :
    coq_Config -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> Coq_ty.coq_Ty -> RiscvPmpProgram.coq_Fun -> bool

  val config_debug_lemma :
    coq_Config -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> RiscvPmpProgram.coq_Lem -> bool

  val default_config : coq_Config

  type 'a coq_SStoreSpec =
    (('a, (RiscvPmpBase.coq_SStore, (RiscvPmpSignature.coq_SHeap,
    RiscvPmpSignature.SymProp.coq_SymProp) RiscvPmpSignature.coq_Impl)
    RiscvPmpSignature.coq_Impl) RiscvPmpSignature.coq_Impl
    RiscvPmpSignature.coq_Box, (RiscvPmpBase.coq_SStore,
    (RiscvPmpSignature.coq_SHeap, RiscvPmpSignature.SymProp.coq_SymProp)
    RiscvPmpSignature.coq_Impl) RiscvPmpSignature.coq_Impl)
    RiscvPmpSignature.coq_Impl

  type coq_ExecCall =
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> RiscvPmpProgram.coq_Fun -> (RiscvPmpBase.coq_SStore,
    RiscvPmpBase.coq_Term RiscvPmpSignature.coq_SHeapSpec)
    RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

  type coq_ExecCallForeign =
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> RiscvPmpProgram.coq_FunX -> (RiscvPmpBase.coq_SStore,
    RiscvPmpBase.coq_Term RiscvPmpSignature.coq_SHeapSpec)
    RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

  type coq_ExecLemma =
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpProgram.coq_Lem -> (RiscvPmpBase.coq_SStore,
    RiscvPmpBase.coq_Unit RiscvPmpSignature.coq_SHeapSpec)
    RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

  type coq_ExecFail =
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> Coq_ty.coq_Val -> RiscvPmpBase.coq_Term coq_SStoreSpec
    RiscvPmpSignature.coq_Valid

  type coq_Exec =
    (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> RiscvPmpProgram.coq_Stm -> RiscvPmpBase.coq_Term
    coq_SStoreSpec RiscvPmpSignature.coq_Valid

  module SStoreSpec :
   sig
    val evalStoreSpec :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
      coq_SStoreSpec, (RiscvPmpBase.coq_SStore, 'a1
      RiscvPmpSignature.coq_SHeapSpec) RiscvPmpSignature.coq_Impl)
      RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

    val lift_purespec :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
      RiscvPmpSignature.coq_SPureSpec, 'a1 coq_SStoreSpec)
      RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

    val lift_heapspec :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
      RiscvPmpSignature.coq_SHeapSpec, 'a1 coq_SStoreSpec)
      RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

    val pure :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1, 'a1
      coq_SStoreSpec) RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

    val bind :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
      coq_SStoreSpec, (('a1, 'a2 coq_SStoreSpec) RiscvPmpSignature.coq_Impl
      RiscvPmpSignature.coq_Box, 'a2 coq_SStoreSpec)
      RiscvPmpSignature.coq_Impl) RiscvPmpSignature.coq_Impl
      RiscvPmpSignature.coq_Valid

    val error :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      ((RiscvPmpBase.coq_SStore, (RiscvPmpSignature.coq_SHeap,
      RiscvPmpBase.Coq_amsg.coq_AMessage) RiscvPmpSignature.coq_Impl)
      RiscvPmpSignature.coq_Impl, 'a1 coq_SStoreSpec)
      RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

    val block :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> 'a1
      coq_SStoreSpec RiscvPmpSignature.coq_Valid

    val angelic_binary :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
      coq_SStoreSpec, ('a1 coq_SStoreSpec, 'a1 coq_SStoreSpec)
      RiscvPmpSignature.coq_Impl) RiscvPmpSignature.coq_Impl
      RiscvPmpSignature.coq_Valid

    val demonic_binary :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> ('a1
      coq_SStoreSpec, ('a1 coq_SStoreSpec, 'a1 coq_SStoreSpec)
      RiscvPmpSignature.coq_Impl) RiscvPmpSignature.coq_Impl
      RiscvPmpSignature.coq_Valid

    val angelic :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar
      option -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term coq_SStoreSpec)
      RiscvPmpSignature.coq_Forall RiscvPmpSignature.coq_Valid

    val demonic :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> lVar
      option -> (Coq_ty.coq_Ty, RiscvPmpBase.coq_Term coq_SStoreSpec)
      RiscvPmpSignature.coq_Forall RiscvPmpSignature.coq_Valid

    val debug :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      ((RiscvPmpBase.coq_SStore, (RiscvPmpSignature.coq_SHeap,
      RiscvPmpBase.Coq_amsg.coq_AMessage) RiscvPmpSignature.coq_Impl)
      RiscvPmpSignature.coq_Impl, ('a1 coq_SStoreSpec, 'a1 coq_SStoreSpec)
      RiscvPmpSignature.coq_Impl) RiscvPmpSignature.coq_Impl
      RiscvPmpSignature.coq_Valid

    val angelic_ctx :
      ('a1 -> lVar) -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx, ('a1, Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) namedEnv
      coq_SStoreSpec) RiscvPmpSignature.coq_Forall RiscvPmpSignature.coq_Valid

    val demonic_ctx :
      ('a1 -> lVar) -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> (('a1, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx, ('a1, Coq_ty.coq_Ty, RiscvPmpBase.coq_Term) namedEnv
      coq_SStoreSpec) RiscvPmpSignature.coq_Forall RiscvPmpSignature.coq_Valid

    module Coq_notations :
     sig
     end

    val demonic_pattern_match :
      ('a1 -> lVar) -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> 'a1 RiscvPmpBase.coq_Pattern ->
      (RiscvPmpBase.coq_Term, 'a1 RiscvPmpBase.coq_SMatchResult
      coq_SStoreSpec) RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

    val pushpop :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> pVar ->
      Coq_ty.coq_Ty -> (RiscvPmpBase.coq_Term, ('a1 coq_SStoreSpec, 'a1
      coq_SStoreSpec) RiscvPmpSignature.coq_Impl) RiscvPmpSignature.coq_Impl
      RiscvPmpSignature.coq_Valid

    val pushspops :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (RiscvPmpBase.coq_SStore, ('a1 coq_SStoreSpec, 'a1 coq_SStoreSpec)
      RiscvPmpSignature.coq_Impl) RiscvPmpSignature.coq_Impl
      RiscvPmpSignature.coq_Valid

    val get_local :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_SStore coq_SStoreSpec RiscvPmpSignature.coq_Valid

    val put_local :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (RiscvPmpBase.coq_SStore, RiscvPmpBase.coq_Unit coq_SStoreSpec)
      RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

    val eval_exp :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> RiscvPmpBase.coq_Exp -> RiscvPmpBase.coq_Term
      coq_SStoreSpec RiscvPmpSignature.coq_Valid

    val eval_exps :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (pVar,
      Coq_ty.coq_Ty, RiscvPmpBase.coq_Exp) namedEnv ->
      RiscvPmpBase.coq_SStore coq_SStoreSpec RiscvPmpSignature.coq_Valid

    val assign :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> pVar ->
      Coq_ty.coq_Ty -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
      Coq_ctx.coq_In -> (RiscvPmpBase.coq_Term, RiscvPmpBase.coq_Unit
      coq_SStoreSpec) RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

    val exec_aux :
      coq_ExecCallForeign -> coq_ExecLemma -> coq_ExecCall -> coq_ExecFail ->
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> RiscvPmpProgram.coq_Stm -> RiscvPmpBase.coq_Term
      coq_SStoreSpec RiscvPmpSignature.coq_Valid
   end

  val exec_contract :
    coq_Exec -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> RiscvPmpSignature.coq_SepContract ->
    RiscvPmpProgram.coq_Stm -> RiscvPmpBase.coq_Unit
    RiscvPmpSignature.coq_SHeapSpec RiscvPmpSignature.coq_Valid

  val exec_call_error_no_fuel : coq_ExecCall

  val sexec_call_foreign : coq_ExecCallForeign

  val debug_lemma :
    coq_Config -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> RiscvPmpProgram.coq_Lem -> (RiscvPmpBase.coq_SStore,
    RiscvPmpBase.coq_Unit RiscvPmpSignature.coq_SHeapSpec)
    RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

  val sexec_lemma : coq_Config -> coq_ExecLemma

  val debug_call :
    coq_Config -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx
    -> Coq_ty.coq_Ty -> RiscvPmpProgram.coq_Fun -> (RiscvPmpBase.coq_SStore,
    RiscvPmpBase.coq_Unit RiscvPmpSignature.coq_SHeapSpec)
    RiscvPmpSignature.coq_Impl RiscvPmpSignature.coq_Valid

  val sexec_fail : coq_ExecFail

  val sexec_call : coq_Config -> nat -> coq_ExecCall

  val sexec : coq_Config -> nat -> coq_Exec

  val vcgen :
    coq_Config -> nat -> (pVar, Coq_ty.coq_Ty) Binding.coq_Binding
    Coq_ctx.coq_Ctx -> Coq_ty.coq_Ty -> RiscvPmpSignature.coq_SepContract ->
    RiscvPmpProgram.coq_Stm -> RiscvPmpSignature.SymProp.coq_SymProp
    RiscvPmpSignature.coq_Valid

  module Symbolic :
   sig
    val verification_failed_with_error :
      RiscvPmpBase.Coq_amsg.coq_EAMessage -> bool

    val ok' :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpSignature.SymProp.coq_SymProp -> bool

    val ok :
      (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpSignature.SymProp.coq_SymProp -> bool

    val coq_VcGenErasureFuel :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> nat -> RiscvPmpSignature.coq_SepContract ->
      RiscvPmpProgram.coq_Stm -> RiscvPmpSignature.Erasure.coq_ESymProp

    val coq_VcGenErasure :
      (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      Coq_ty.coq_Ty -> RiscvPmpSignature.coq_SepContract ->
      RiscvPmpProgram.coq_Stm -> RiscvPmpSignature.Erasure.coq_ESymProp

    module Statistics :
     sig
      val extend_postcond_with_debug :
        (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> RiscvPmpSignature.coq_SepContract ->
        RiscvPmpSignature.coq_SepContract

      val calc :
        (pVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
        Coq_ty.coq_Ty -> RiscvPmpProgram.coq_Fun -> stats option
     end
   end
 end

val exec_instruction_prologue : aST -> RiscvPmpSignature.Coq_asn.coq_Assertion

val exec_instruction_epilogue : aST -> RiscvPmpSignature.Coq_asn.coq_Assertion

val sexec_instruction :
  aST -> (RiscvPmpBase.coq_Term, RiscvPmpBase.coq_Term
  RiscvPmpSignature.coq_SHeapSpec) RiscvPmpSignature.coq_Impl
  RiscvPmpSignature.coq_Valid

val sexec_block_addr :
  aST list -> (RiscvPmpBase.coq_Term, (RiscvPmpBase.coq_Term,
  RiscvPmpBase.coq_Term RiscvPmpSignature.coq_SHeapSpec)
  RiscvPmpSignature.coq_Impl) RiscvPmpSignature.coq_Impl
  RiscvPmpSignature.coq_Valid

val sexec_triple_addr :
  (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
  RiscvPmpSignature.Coq_asn.coq_Assertion -> aST list ->
  RiscvPmpSignature.Coq_asn.coq_Assertion -> RiscvPmpBase.coq_Unit
  RiscvPmpSignature.coq_SHeapSpec RiscvPmpSignature.coq_Valid

val sblock_verification_condition :
  (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
  RiscvPmpSignature.Coq_asn.coq_Assertion -> aST list ->
  RiscvPmpSignature.Coq_asn.coq_Assertion ->
  RiscvPmpSignature.SymProp.coq_SymProp RiscvPmpSignature.coq_Valid

module Examples :
 sig
  val minimal_pre :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpSignature.Coq_asn.coq_Assertion

  val minimal_post :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpSignature.Coq_asn.coq_Assertion

  val extend_to_minimal_pre :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpSignature.Coq_asn.coq_Assertion ->
    RiscvPmpSignature.Coq_asn.coq_Assertion

  val extend_to_minimal_post :
    (lVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpSignature.Coq_asn.coq_Assertion ->
    RiscvPmpSignature.Coq_asn.coq_Assertion

  val coq_VC_triple :
    (string, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpSignature.Coq_asn.coq_Assertion -> aST list ->
    RiscvPmpSignature.Coq_asn.coq_Assertion ->
    RiscvPmpSignature.SymProp.coq_SymProp

  type coq_BlockVerifierContract = { precondition : RiscvPmpSignature.Coq_asn.coq_Assertion;
                                     instrs : aST list;
                                     postcondition : RiscvPmpSignature.Coq_asn.coq_Assertion }

  val exec_VC :
    (string, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    coq_BlockVerifierContract -> RiscvPmpSignature.SymProp.coq_SymProp
 end
