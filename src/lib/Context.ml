open Ascii
open BinNat
open BinNums
open Classes
open Datatypes
open DecimalString
open List
open PeanoNat
open Prelude
open Specif
open String

type __ = Obj.t

module Binding =
 struct
  type ('n, 't) coq_Binding = { name : 'n; coq_type : 't }
 end

module Coq_ctx =
 struct
  type 'b coq_Ctx =
  | Coq_nil
  | Coq_snoc of 'b coq_Ctx * 'b

  (** val coq_Ctx_rect :
      'a2 -> ('a1 coq_Ctx -> 'a2 -> 'a1 -> 'a2) -> 'a1 coq_Ctx -> 'a2 **)

  let rec coq_Ctx_rect f f0 = function
  | Coq_nil -> f
  | Coq_snoc (_UU0393_, b) -> f0 _UU0393_ (coq_Ctx_rect f f0 _UU0393_) b

  (** val coq_NoConfusionPackage_Ctx : 'a1 coq_Ctx coq_NoConfusionPackage **)

  let coq_NoConfusionPackage_Ctx =
    Build_NoConfusionPackage

  (** val eq_dec_ctx : 'a1 coq_EqDec -> 'a1 coq_Ctx coq_EqDec **)

  let rec eq_dec_ctx eqB _UU0393_ _UU0394_ =
    match _UU0393_ with
    | Coq_nil ->
      (match _UU0394_ with
       | Coq_nil -> Coq_left
       | Coq_snoc (_, _) -> Coq_right)
    | Coq_snoc (_UU0393_0, b) ->
      (match _UU0394_ with
       | Coq_nil -> Coq_right
       | Coq_snoc (_UU0394_0, c) ->
         f_equal2_dec (fun x x0 -> Coq_snoc (x, x0)) _UU0393_0 _UU0394_0 b c
           (eq_dec_ctx eqB _UU0393_0 _UU0394_0) (eq_dec eqB b c))

  (** val cat : 'a1 coq_Ctx -> 'a1 coq_Ctx -> 'a1 coq_Ctx **)

  let rec cat _UU0393_1 = function
  | Coq_nil -> _UU0393_1
  | Coq_snoc (_UU0393_3, _UU03c4_) ->
    Coq_snoc ((cat _UU0393_1 _UU0393_3), _UU03c4_)

  type 'b coq_In = nat
    (* singleton inductive, whose constructor was MkIn *)

  (** val in_zero : 'a1 -> 'a1 coq_Ctx -> 'a1 coq_In **)

  let in_zero _ _ =
    O

  (** val in_succ : 'a1 -> 'a1 coq_Ctx -> 'a1 -> 'a1 coq_In -> 'a1 coq_In **)

  let in_succ _ _ _ bIn =
    S bIn

  (** val coq_In_case :
      ('a1 -> 'a1 coq_Ctx -> 'a2) -> ('a1 -> 'a1 coq_Ctx -> 'a1 -> 'a1 coq_In
      -> 'a2) -> 'a1 -> 'a1 coq_Ctx -> 'a1 coq_In -> 'a2 **)

  let coq_In_case fz fs b _UU0393_ i =
    match _UU0393_ with
    | Coq_nil -> assert false (* absurd case *)
    | Coq_snoc (_UU0393_0, b') ->
      (match i with
       | O -> fz b' _UU0393_0
       | S n -> fs b' _UU0393_0 b n)

  (** val coq_In_rect :
      ('a1 -> 'a1 coq_Ctx -> 'a2) -> ('a1 -> 'a1 coq_Ctx -> 'a1 -> 'a1 coq_In
      -> 'a2 -> 'a2) -> 'a1 -> 'a1 coq_Ctx -> 'a1 coq_In -> 'a2 **)

  let rec coq_In_rect fz fs b _UU0393_ bIn =
    coq_In_case fz (fun b' _UU0393_0 b0 bIn0 ->
      fs b0 _UU0393_0 b' bIn0 (coq_In_rect fz fs b0 _UU0393_0 bIn0)) b
      _UU0393_ bIn

  type 'b coq_SnocView =
  | Coq_isZero
  | Coq_isSucc of 'b * 'b coq_In

  (** val view : 'a1 -> 'a1 coq_Ctx -> 'a1 coq_In -> __ **)

  let view b =
    coq_In_case (Obj.magic (fun _ _ -> Coq_isZero))
      (Obj.magic (fun _ _ x x0 -> Coq_isSucc (x, x0))) b

  (** val in_cat_left :
      'a1 -> 'a1 coq_Ctx -> 'a1 coq_Ctx -> 'a1 coq_In -> 'a1 coq_In **)

  let rec in_cat_left b _UU0393_ _UU0394_ bIn =
    match _UU0394_ with
    | Coq_nil -> bIn
    | Coq_snoc (_UU0394_0, b0) ->
      in_succ b (cat _UU0393_ _UU0394_0) b0
        (in_cat_left b _UU0393_ _UU0394_0 bIn)

  (** val in_cat_right :
      'a1 -> 'a1 coq_Ctx -> 'a1 coq_Ctx -> 'a1 coq_In -> 'a1 coq_In **)

  let rec in_cat_right b _UU0393_ _UU0394_ bIn =
    coq_In_case (fun b0 _UU0394_0 -> in_zero b0 (cat _UU0393_ _UU0394_0))
      (fun b' _UU0393_0 b0 i ->
      in_succ b0 (cat _UU0393_ _UU0393_0) b'
        (in_cat_right b0 _UU0393_ _UU0393_0 i))
      b _UU0394_ bIn

  type 'b coq_CatView =
  | Coq_isCatLeft of 'b coq_In
  | Coq_isCatRight of 'b coq_In

  (** val catView :
      'a1 coq_Ctx -> 'a1 coq_Ctx -> 'a1 -> 'a1 coq_In -> 'a1 coq_CatView **)

  let rec catView _UU0393_ = function
  | Coq_nil -> Obj.magic (fun _ x -> Coq_isCatLeft x)
  | Coq_snoc (_UU0394_0, b') ->
    (fun b bIn ->
      match Obj.magic view b (cat _UU0393_ (Coq_snoc (_UU0394_0, b'))) bIn with
      | Coq_isZero -> Coq_isCatRight (in_zero b' _UU0394_0)
      | Coq_isSucc (b0, bIn0) ->
        (match catView _UU0393_ _UU0394_0 b0 bIn0 with
         | Coq_isCatLeft bIn1 -> Coq_isCatLeft bIn1
         | Coq_isCatRight bIn1 ->
           Coq_isCatRight (in_succ b0 _UU0394_0 b' bIn1)))

  (** val coq_In_eqb :
      'a1 coq_Ctx -> 'a1 -> 'a1 -> 'a1 coq_In -> 'a1 coq_In -> bool **)

  let coq_In_eqb _ _ _ =
    Nat.eqb

  (** val coq_In_eqb_spec :
      'a1 coq_Ctx -> 'a1 -> 'a1 -> 'a1 coq_In -> 'a1 coq_In -> reflect **)

  let coq_In_eqb_spec _ _ _ =
    Nat.eqb_spec

  type ('b, 'p) coq_All =
  | Coq_all_nil
  | Coq_all_snoc of 'b coq_Ctx * 'b * ('b, 'p) coq_All * 'p

  (** val all_intro : ('a1 -> 'a2) -> 'a1 coq_Ctx -> ('a1, 'a2) coq_All **)

  let rec all_intro hP = function
  | Coq_nil -> Coq_all_nil
  | Coq_snoc (_UU0393_0, b) ->
    Coq_all_snoc (_UU0393_0, b, (all_intro hP _UU0393_0), (hP b))

  (** val remove : 'a1 coq_Ctx -> 'a1 -> 'a1 coq_In -> 'a1 coq_Ctx **)

  let rec remove _UU0393_ b bIn =
    coq_In_case (fun _ _UU0393_0 -> _UU0393_0) (fun b' _UU0393_0 b0 bIn0 ->
      Coq_snoc ((remove _UU0393_0 b0 bIn0), b')) b _UU0393_ bIn

  (** val shift_var :
      'a1 -> 'a1 -> 'a1 coq_Ctx -> 'a1 coq_In -> 'a1 coq_In -> 'a1 coq_In **)

  let rec shift_var b x _UU0393_ bIn =
    coq_In_case (fun b0 _UU0393_0 xIn ->
      in_succ x (remove (Coq_snoc (_UU0393_0, b0)) b0 (in_zero b0 _UU0393_0))
        b0 xIn)
      (fun b' _UU0393_0 b0 bIn0 xIn ->
      match Obj.magic view x (Coq_snoc ((remove _UU0393_0 b0 bIn0), b')) xIn with
      | Coq_isZero -> in_zero b' _UU0393_0
      | Coq_isSucc (b1, xIn0) ->
        in_succ b1 _UU0393_0 b' (shift_var b0 b1 _UU0393_0 bIn0 xIn0))
      b _UU0393_ bIn

  type 'b coq_OccursCheckView =
  | Same
  | Diff of 'b * 'b coq_In

  (** val occurs_check_view_step :
      'a1 coq_Ctx -> 'a1 -> 'a1 -> 'a1 -> 'a1 coq_In -> 'a1 coq_In -> 'a1
      coq_OccursCheckView -> 'a1 coq_OccursCheckView **)

  let occurs_check_view_step _UU03a3_ b x _ xIn _ = function
  | Same -> Same
  | Diff (y0, yIn) -> Diff (y0, (in_succ y0 (remove _UU03a3_ x xIn) b yIn))

  (** val occurs_check_view :
      'a1 coq_Ctx -> 'a1 -> 'a1 coq_In -> 'a1 -> 'a1 coq_In -> 'a1
      coq_OccursCheckView **)

  let rec occurs_check_view _UU0393_ x xIn =
    coq_In_case (fun x0 _UU0393_0 y yIn ->
      match Obj.magic view y (Coq_snoc (_UU0393_0, x0)) yIn with
      | Coq_isZero -> Same
      | Coq_isSucc (b, yIn0) -> Diff (b, yIn0))
      (fun z _UU0393_0 x0 xIn0 y yIn ->
      match Obj.magic view y (Coq_snoc (_UU0393_0, z)) yIn with
      | Coq_isZero ->
        Diff (z,
          (in_zero z
            (let rec remove0 _UU0393_1 b bIn =
               coq_In_case (fun _ _UU0393_2 -> _UU0393_2)
                 (fun b' _UU0393_2 b0 bIn0 -> Coq_snoc
                 ((remove0 _UU0393_2 b0 bIn0), b')) b _UU0393_1 bIn
             in remove0 _UU0393_0 x0 xIn0)))
      | Coq_isSucc (b, yIn0) ->
        occurs_check_view_step _UU0393_0 z x0 b xIn0 yIn0
          (occurs_check_view _UU0393_0 x0 xIn0 b yIn0))
      x _UU0393_ xIn

  (** val forallb : 'a1 coq_Ctx -> ('a1 -> 'a1 coq_In -> bool) -> bool **)

  let rec forallb _UU0393_ x =
    match _UU0393_ with
    | Coq_nil -> Coq_true
    | Coq_snoc (_UU0393_0, b) ->
      (match x b (in_zero b _UU0393_0) with
       | Coq_true ->
         forallb _UU0393_0 (fun b0 bIn -> x b0 (in_succ b0 _UU0393_0 b bIn))
       | Coq_false -> Coq_false)

  (** val map : ('a1 -> 'a2) -> 'a1 coq_Ctx -> 'a2 coq_Ctx **)

  let rec map f = function
  | Coq_nil -> Coq_nil
  | Coq_snoc (_UU0393_0, a) -> Coq_snoc ((map f _UU0393_0), (f a))

  (** val in_map :
      ('a1 -> 'a2) -> 'a1 -> 'a1 coq_Ctx -> 'a1 coq_In -> 'a2 coq_In **)

  let rec in_map f b _UU0393_ bIn =
    coq_In_case (fun b0 _UU0393_0 ->
      in_zero (f b0)
        (let rec map0 = function
         | Coq_nil -> Coq_nil
         | Coq_snoc (_UU0393_2, a) -> Coq_snoc ((map0 _UU0393_2), (f a))
         in map0 _UU0393_0))
      (fun b' _UU0393_0 b0 bIn0 ->
      in_succ (f b0) (map f _UU0393_0) (f b') (in_map f b0 _UU0393_0 bIn0)) b
      _UU0393_ bIn

  (** val resolve :
      'a1 coq_EqDec -> ('a1, 'a2) Binding.coq_Binding coq_Ctx -> 'a1 -> 'a2
      option **)

  let rec resolve name_eqdec _UU0393_ x =
    match _UU0393_ with
    | Coq_nil -> None
    | Coq_snoc (_UU0393_0, b) ->
      let y = b.Binding.name in
      let d = b.Binding.coq_type in
      (match name_eqdec x y with
       | Coq_left -> Some d
       | Coq_right -> resolve name_eqdec _UU0393_0 x)

  (** val resolve_mk_in :
      'a1 coq_EqDec -> ('a1, 'a2) Binding.coq_Binding coq_Ctx -> 'a1 -> 'a2
      coq_IsSome -> ('a1, 'a2) Binding.coq_Binding coq_In **)

  let rec resolve_mk_in name_eqdec _UU0393_ x =
    match _UU0393_ with
    | Coq_nil -> (fun _ -> assert false (* absurd case *))
    | Coq_snoc (_UU0393_0, b) ->
      let y = b.Binding.name in
      let d = b.Binding.coq_type in
      (fun p ->
      match name_eqdec x y with
      | Coq_left ->
        in_zero { Binding.name = x; Binding.coq_type =
          (fromSome (Some d) p) } _UU0393_0
      | Coq_right ->
        in_succ { Binding.name = x; Binding.coq_type =
          (fromSome (resolve name_eqdec _UU0393_0 x) p) } _UU0393_0
          { Binding.name = y; Binding.coq_type = d }
          (resolve_mk_in name_eqdec _UU0393_0 x p))

  (** val names : ('a1, 'a2) Binding.coq_Binding coq_Ctx -> 'a1 list **)

  let rec names = function
  | Coq_nil -> []
  | Coq_snoc (_UU0393_0, b) -> let y = b.Binding.name in y::(names _UU0393_0)

  (** val split_at_dot' : string -> (string -> string -> 'a1) -> 'a1 **)

  let rec split_at_dot' x k =
    match x with
    | EmptyString -> k EmptyString EmptyString
    | String (a, x0) ->
      let Ascii (b, b0, b1, b2, b3, b4, b5, b6) = a in
      (match b with
       | Coq_true -> split_at_dot' x0 (fun pre -> k (String (a, pre)))
       | Coq_false ->
         (match b0 with
          | Coq_true ->
            (match b1 with
             | Coq_true ->
               (match b2 with
                | Coq_true ->
                  (match b3 with
                   | Coq_true ->
                     split_at_dot' x0 (fun pre -> k (String (a, pre)))
                   | Coq_false ->
                     (match b4 with
                      | Coq_true ->
                        (match b5 with
                         | Coq_true ->
                           split_at_dot' x0 (fun pre -> k (String (a, pre)))
                         | Coq_false ->
                           (match b6 with
                            | Coq_true ->
                              split_at_dot' x0 (fun pre ->
                                k (String (a, pre)))
                            | Coq_false -> k EmptyString x0))
                      | Coq_false ->
                        split_at_dot' x0 (fun pre -> k (String (a, pre)))))
                | Coq_false ->
                  split_at_dot' x0 (fun pre -> k (String (a, pre))))
             | Coq_false -> split_at_dot' x0 (fun pre -> k (String (a, pre))))
          | Coq_false -> split_at_dot' x0 (fun pre -> k (String (a, pre)))))

  (** val split_at_dot : string -> (string, string) prod **)

  let split_at_dot x =
    split_at_dot' x (fun x0 x1 -> Coq_pair (x0, x1))

  (** val parse_number : string -> coq_N **)

  let parse_number x =
    match NilEmpty.uint_of_string x with
    | Some n -> N.of_uint n
    | None -> N0

  (** val unparse_number : coq_N -> string **)

  let unparse_number x =
    NilEmpty.string_of_uint (N.to_uint x)

  (** val max_with_base : string -> string list -> coq_N **)

  let max_with_base base xs =
    fold_left (fun o x ->
      let Coq_pair (pre, suf) = split_at_dot x in
      (match eqb pre base with
       | Coq_true -> N.max o (parse_number suf)
       | Coq_false -> o))
      xs N0

  (** val fresh :
      (string, 'a1) Binding.coq_Binding coq_Ctx -> string option -> string **)

  let fresh xs x =
    let xs0 = names xs in
    let x0 =
      match x with
      | Some x0 -> x0
      | None ->
        String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
          Coq_true, Coq_true, Coq_false)), EmptyString)
    in
    (match find (eqb x0) xs0 with
     | Some _ ->
       let base = fst (split_at_dot x0) in
       let n = N.succ (max_with_base base xs0) in
       append base (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_false, Coq_false)), (unparse_number n)))
     | None -> x0)
 end
