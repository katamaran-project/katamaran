(* Reification of the erased symbolic propositions (Erasure.ESymProp) produced
   by the symbolic executor into Ltac2 data, and reflection of that data back
   into a Gallina Prop with named, freshened variables. The main entry point is
   the Ltac1 tactic [reify_vc], which replaces a goal
   [VerificationConditionWithErasure p] with a readable Prop that is
   convertible to it.

   This is specific to the RiscvPmp case study: symbolic variable names
   (LVar) are assumed to be string literals. *)

(* Needed by the StringToIdent snippet below. *)
From Stdlib Require Import
     Lists.List
     Strings.String.
From Stdlib Require Import
     Init.Byte.
Import ListNotations.

(* C&P from Iris/iris/proofmode/string_ident.v
   https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/proofmode/string_ident.v?ref_type=heads#L64-65
 *)

Module StringToIdent.
From Ltac2 Require Import Ltac2.
  Ltac2 Type exn ::= [ NotStringLiteral(constr) | InvalidIdent(string) ].

  Ltac2 coq_byte_to_int (b : constr) : int :=
    match! b with
    (* generate this line with python3 -c 'print(" ".join([\'| x%02x => %d\' % (x,x) for x in range(256)]))' *)
    | x00 => 0 | x01 => 1 | x02 => 2 | x03 => 3 | x04 => 4 | x05 => 5 | x06 => 6 | x07 => 7 | x08 => 8 | x09 => 9 | x0a => 10 | x0b => 11 | x0c => 12 | x0d => 13 | x0e => 14 | x0f => 15 | x10 => 16 | x11 => 17 | x12 => 18 | x13 => 19 | x14 => 20 | x15 => 21 | x16 => 22 | x17 => 23 | x18 => 24 | x19 => 25 | x1a => 26 | x1b => 27 | x1c => 28 | x1d => 29 | x1e => 30 | x1f => 31 | x20 => 32 | x21 => 33 | x22 => 34 | x23 => 35 | x24 => 36 | x25 => 37 | x26 => 38 | x27 => 39 | x28 => 40 | x29 => 41 | x2a => 42 | x2b => 43 | x2c => 44 | x2d => 45 | x2e => 46 | x2f => 47 | x30 => 48 | x31 => 49 | x32 => 50 | x33 => 51 | x34 => 52 | x35 => 53 | x36 => 54 | x37 => 55 | x38 => 56 | x39 => 57 | x3a => 58 | x3b => 59 | x3c => 60 | x3d => 61 | x3e => 62 | x3f => 63 | x40 => 64 | x41 => 65 | x42 => 66 | x43 => 67 | x44 => 68 | x45 => 69 | x46 => 70 | x47 => 71 | x48 => 72 | x49 => 73 | x4a => 74 | x4b => 75 | x4c => 76 | x4d => 77 | x4e => 78 | x4f => 79 | x50 => 80 | x51 => 81 | x52 => 82 | x53 => 83 | x54 => 84 | x55 => 85 | x56 => 86 | x57 => 87 | x58 => 88 | x59 => 89 | x5a => 90 | x5b => 91 | x5c => 92 | x5d => 93 | x5e => 94 | x5f => 95 | x60 => 96 | x61 => 97 | x62 => 98 | x63 => 99 | x64 => 100 | x65 => 101 | x66 => 102 | x67 => 103 | x68 => 104 | x69 => 105 | x6a => 106 | x6b => 107 | x6c => 108 | x6d => 109 | x6e => 110 | x6f => 111 | x70 => 112 | x71 => 113 | x72 => 114 | x73 => 115 | x74 => 116 | x75 => 117 | x76 => 118 | x77 => 119 | x78 => 120 | x79 => 121 | x7a => 122 | x7b => 123 | x7c => 124 | x7d => 125 | x7e => 126 | x7f => 127 | x80 => 128 | x81 => 129 | x82 => 130 | x83 => 131 | x84 => 132 | x85 => 133 | x86 => 134 | x87 => 135 | x88 => 136 | x89 => 137 | x8a => 138 | x8b => 139 | x8c => 140 | x8d => 141 | x8e => 142 | x8f => 143 | x90 => 144 | x91 => 145 | x92 => 146 | x93 => 147 | x94 => 148 | x95 => 149 | x96 => 150 | x97 => 151 | x98 => 152 | x99 => 153 | x9a => 154 | x9b => 155 | x9c => 156 | x9d => 157 | x9e => 158 | x9f => 159 | xa0 => 160 | xa1 => 161 | xa2 => 162 | xa3 => 163 | xa4 => 164 | xa5 => 165 | xa6 => 166 | xa7 => 167 | xa8 => 168 | xa9 => 169 | xaa => 170 | xab => 171 | xac => 172 | xad => 173 | xae => 174 | xaf => 175 | xb0 => 176 | xb1 => 177 | xb2 => 178 | xb3 => 179 | xb4 => 180 | xb5 => 181 | xb6 => 182 | xb7 => 183 | xb8 => 184 | xb9 => 185 | xba => 186 | xbb => 187 | xbc => 188 | xbd => 189 | xbe => 190 | xbf => 191 | xc0 => 192 | xc1 => 193 | xc2 => 194 | xc3 => 195 | xc4 => 196 | xc5 => 197 | xc6 => 198 | xc7 => 199 | xc8 => 200 | xc9 => 201 | xca => 202 | xcb => 203 | xcc => 204 | xcd => 205 | xce => 206 | xcf => 207 | xd0 => 208 | xd1 => 209 | xd2 => 210 | xd3 => 211 | xd4 => 212 | xd5 => 213 | xd6 => 214 | xd7 => 215 | xd8 => 216 | xd9 => 217 | xda => 218 | xdb => 219 | xdc => 220 | xdd => 221 | xde => 222 | xdf => 223 | xe0 => 224 | xe1 => 225 | xe2 => 226 | xe3 => 227 | xe4 => 228 | xe5 => 229 | xe6 => 230 | xe7 => 231 | xe8 => 232 | xe9 => 233 | xea => 234 | xeb => 235 | xec => 236 | xed => 237 | xee => 238 | xef => 239 | xf0 => 240 | xf1 => 241 | xf2 => 242 | xf3 => 243 | xf4 => 244 | xf5 => 245 | xf6 => 246 | xf7 => 247 | xf8 => 248 | xf9 => 249 | xfa => 250 | xfb => 251 | xfc => 252 | xfd => 253 | xfe => 254 | xff => 255
    end.

  Ltac2 coq_byte_to_char (b : constr) : char :=
    Char.of_int (coq_byte_to_int b).

  Fixpoint coq_string_to_list_byte (s : string) : list byte :=
    match s with
    | EmptyString => []
    | String c s => Ascii.byte_of_ascii c :: coq_string_to_list_byte s
    end.

  (** copy a list of Coq byte constrs into a string (already of the right length) *)
  Ltac2 rec coq_byte_list_blit_list (pos : int) (ls : constr) (str : string) : unit :=
    match! ls with
    | nil => ()
    | ?c :: ?ls =>
      let b := coq_byte_to_char c in
      String.set str pos b; coq_byte_list_blit_list (Int.add pos 1) ls str
    end.

  Ltac2 rec coq_string_length (s : constr) : int :=
    match! s with
    | EmptyString => 0
    | String _ ?s' => Int.add 1 (coq_string_length s')
    | _ => Control.throw (NotStringLiteral s)
    end.

  Ltac2 compute (c : constr) : constr :=
    Std.eval_vm None c.

  (** [coq_string_to_string] converts a Gallina string in a constr to an Ltac2
  native string *)
  Ltac2 coq_string_to_string (s : constr) : string :=
    let l := coq_string_length s in
    let str := String.make l (Char.of_int 0) in
    let bytes := compute constr:(coq_string_to_list_byte $s) in
    let _ := coq_byte_list_blit_list 0 bytes str in
    str.

  Ltac2 string_to_ident (s : string) : ident :=
    match Ident.of_string s with
    | Some id => id
    | None => Control.throw (InvalidIdent s)
    end.

End StringToIdent.

From Katamaran Require Import
     Context
     Environment
     Syntax.BinOps
     Syntax.TypeDecl
     Syntax.UnOps
     RiscvPmp.Base
     RiscvPmp.Sig
     RiscvPmp.Logic.

Import RiscvPmpExecutor.

From Ltac2 Require Import
     Ltac2
     Printf.

(* Importing Ltac2 makes it the default proof mode again; force Ltac1. *)
Set Default Proof Mode "Classic".

Import Erasure.

(* ------------------------------------------------------------------------ *)
(* Generic helpers                                                           *)
(* ------------------------------------------------------------------------ *)

Ltac2 rec nat_to_int (n : constr) : int :=
  lazy_match! n with
  | O => 0
  | S ?m => Int.add 1 (nat_to_int m)
  | _ => Control.throw (Tactic_failure (Some (fprintf "reify: expected a nat literal but got '%t'" n)))
  end.

(* [string_init n f] is the string of length [n] whose [i]-th character is
   [f i]. Ltac2 strings are mutable but have a fixed length, so we allocate the
   whole string up front and fill it in. *)
Ltac2 string_init (n : int) (f : int -> char) : string :=
  let r := String.make n (Char.of_int 0) in
  let rec fill (i : int) :=
    if Int.lt i n then (String.set r i (f i); fill (Int.add i 1)) else () in
  fill 0;
  r.

Ltac2 rec list_remove (l : 'a list) (n : int) : 'a list :=
  match l with
  | [] => []
  | x :: xs => if Int.equal n 0 then xs else x :: list_remove xs (Int.sub n 1)
  end.

(* ------------------------------------------------------------------------ *)
(* Named variables                                                           *)
(* ------------------------------------------------------------------------ *)
(* Turn the names of symbolic variables into valid, fresh identifiers (using the
   StringToIdent snippet) and introduce variables carrying those names. *)

(* Turn the name of a symbolic variable into a valid identifier using the
   string_ident snippet from Iris. Names like "L.1" are not identifiers, so
   we sanitise them first (and let Fresh.fresh pick the final name). *)
Ltac2 sanitise_char (c : char) : char :=
  let i := Char.to_int c in
  if Bool.or (Bool.and (Int.le 48 i) (Int.le i 57))      (* 0-9 *)
       (Bool.or (Bool.and (Int.le 65 i) (Int.le i 90))   (* A-Z *)
          (Bool.or (Bool.and (Int.le 97 i) (Int.le i 122)) (* a-z *)
             (Bool.or (Int.equal i 95) (Int.equal i 39)))) (* _ ' *)
  then c else Char.of_int 95. (*i.e. `_` *)

Ltac2 sanitise_string (s : string) : string :=
  (* Drop the ".<n>" suffix of renamed variables ("L.1" ↦ "L"); Fresh.fresh
     makes the names unique again. *)
  let len := String.length s in
  let rec find_dot (i : int) :=
    if Int.lt i len then (if Int.equal (Char.to_int (String.get s i)) 46 then i else find_dot (Int.add i 1))
    else len in
  let n := find_dot 0 in
  let r := string_init n (fun i => sanitise_char (String.get s i)) in
  (* identifiers cannot start with a digit or a quote *)
  if Int.equal n 0 then "x"
  else
    let i0 := Char.to_int (String.get r 0) in
    if Bool.or (Bool.and (Int.le 48 i0) (Int.le i0 57)) (Int.equal i0 39)
    then String.concat "" ["x"; r] else r.

Ltac2 binder_ident (name : string) : ident :=
  let s := sanitise_string name in
  match Ident.of_string s with
  | Some id => id
  | None =>
      (* e.g. a reserved word *)
      StringToIdent.string_to_ident (String.concat "" [s; "_"])
  end.

(* [with_var name lt k] builds a lambda [fun x : Val lt => k x], where [x] is a fresh
   variable named after [lv], and [k] receives the variable together with its
   type so that terms inside can refer to it. *)
Ltac2 with_var (name : string) (lt : constr) (k : constr -> constr) : constr :=
  let base := binder_ident name in
  let id := Fresh.fresh (Fresh.Free.of_goal ()) base in
  Constr.in_context id constr:(Val $lt)
    (fun () => Control.refine (fun () => k (Control.hyp id))).

(* ------------------------------------------------------------------------ *)
(* Reified representation                                                    *)
(* ------------------------------------------------------------------------ *)
(* Erased symbolic propositions as Ltac2 data, following ETerm, EFormula and
   ESymProp. [constr] fields are kept for what is simply spliced back into the
   result: operators, values and types. *)

Ltac2 Type rec term := [
  | Var (int)                                        (* de Bruijn index *)
  | Val (constr)                                     (* v *)
  | Binop (constr, term, term)                       (* op t1 t2 *)
  | Unop (constr, term)                              (* op t *)
  | Tuple (eenv)                                     (* ts *)
  | Union (constr, constr, term)                     (* U K t *)
  | Record (constr, eenv)                            (* R ts *)
  ]
(* An environment of terms, innermost entry first. The nil constructor only
   records the type B of the bindings; a snoc has B, the binding and the term. *)
with eenv := [
  | EnvNil (constr)
  | EnvSnoc (constr, constr, term, eenv)
  ].

Ltac2 Type rec formula := [
  | User (constr, eenv)                              (* p ts *)
  | Bool (term)
  | Relop (constr, term, term)                       (* op t1 t2 *)
  | FTrue
  | FFalse
  | And (formula, formula)
  | Or (formula, formula)
  ].

Ltac2 Type rec symprop := [
  | AngelicBin (symprop, symprop)
  | DemonicBin (symprop, symprop)
  | Error
  | Block
  | AssertK (formula, symprop)
  | AssumeK (formula, symprop)
  | Angelic (string, constr, symprop)                (* name σ k *)
  | Demonic (string, constr, symprop)
  | AssertVarEq (int, term, symprop)                 (* n t k *)
  | AssumeVarEq (int, term, symprop)
  ].

(* ------------------------------------------------------------------------ *)
(* Reification: ESymProp to Ltac2 data                                       *)
(* ------------------------------------------------------------------------ *)
(* Pattern matching is not supported and neither is the debug information,
   which inst_symprop ignores. *)

(* Split a `MkB lv lt` binder into its name and type, ignoring the implicit
   arguments (pattern matching on MkB fails on the real VC). *)
Ltac2 split_binder (b : constr) : constr * constr :=
  match Constr.Unsafe.kind b with
  | Constr.Unsafe.App _ args =>
      if Int.equal (Array.length args) 4
      then (Array.get args 2, Array.get args 3)
      else Control.zero (Tactic_failure (Some (fprintf "reify: unexpected binder '%t'" b)))
  | _ => Control.zero (Tactic_failure (Some (fprintf "reify: unexpected binder '%t'" b)))
  end.

Ltac2 rec reify_term (st : constr) : term :=
  lazy_match! st with
  | @eterm_var _ _ ?n => Var (nat_to_int n)
  | eterm_val _ ?v => Val v
  | @eterm_binop _ _ _ ?op ?t1 ?t2 => Binop op (reify_term t1) (reify_term t2)
  | @eterm_unop _ _ ?op ?t => Unop op (reify_term t)
  | @eterm_tuple _ ?ts => Tuple (reify_env ts)
  | @eterm_union ?u ?k ?t => Union u k (reify_term t)
  | eterm_record ?r ?ts => Record r (reify_env ts)
  | _ => Control.zero (Tactic_failure (Some (fprintf "reify: unknown ETerm constructor in '%t'" st)))
  end

with reify_env (e : constr) : eenv :=
  lazy_match! e with
  | @env.nil ?b _ => EnvNil b
  | @env.snoc ?b _ _ ?e' ?bb ?t => EnvSnoc b bb (reify_term t) (reify_env e')
  | _ => Control.zero (Tactic_failure (Some (fprintf "reify: unexpected environment '%t'" e)))
  end.

Ltac2 rec reify_formula (f : constr) : formula :=
  lazy_match! f with
  | @eformula_user ?p ?ts => User p (reify_env ts)
  | eformula_bool ?t => Bool (reify_term t)
  | @eformula_relop _ ?op ?t1 ?t2 => Relop op (reify_term t1) (reify_term t2)
  | eformula_true => FTrue
  | eformula_false => FFalse
  | eformula_and ?a ?b => And (reify_formula a) (reify_formula b)
  | eformula_or ?a ?b => Or (reify_formula a) (reify_formula b)
  | _ => Control.zero (Tactic_failure (Some (fprintf "reify: unknown EFormula constructor in '%t'" f)))
  end.

Ltac2 rec reify_sp (sp : constr) : symprop :=
  lazy_match! sp with
  | eangelic_binary ?a ?b => AngelicBin (reify_sp a) (reify_sp b)
  | edemonic_binary ?a ?b => DemonicBin (reify_sp a) (reify_sp b)
  | eerror _ => Error
  | eblock => Block
  | eassertk ?f ?k => AssertK (reify_formula f) (reify_sp k)
  | eassumek ?f ?k => AssumeK (reify_formula f) (reify_sp k)
  | eangelicv ?binder ?k =>
      let (lv, lt) := split_binder binder in
      Angelic (StringToIdent.coq_string_to_string lv) lt (reify_sp k)
  | edemonicv ?binder ?k =>
      let (lv, lt) := split_binder binder in
      Demonic (StringToIdent.coq_string_to_string lv) lt (reify_sp k)
  | @eassert_vareq _ _ ?n ?t ?k => AssertVarEq (nat_to_int n) (reify_term t) (reify_sp k)
  | @eassume_vareq _ _ ?n ?t ?k => AssumeVarEq (nat_to_int n) (reify_term t) (reify_sp k)
  | edebug _ ?k => reify_sp k
  | epattern_match _ _ _ =>
      Control.zero (Tactic_failure (Some (fprintf "reify: pattern matching is not supported in '%t'" sp)))
  | epattern_match_var _ _ _ _ =>
      Control.zero (Tactic_failure (Some (fprintf "reify: pattern matching is not supported in '%t'" sp)))
  | _ => Control.zero (Tactic_failure (Some (fprintf "reify: unknown ESymProp constructor in '%t'" sp)))
  end.

(* ------------------------------------------------------------------------ *)
(* Reflection: Ltac2 data to Prop                                            *)
(* ------------------------------------------------------------------------ *)

(* The domain of the environment of values matching an environment of terms
   over B. *)
Ltac2 val_dom (b : constr) : constr :=
  if Constr.equal b constr:(Ty) then constr:(Val)
  else constr:(fun xt : $b => Val (type xt)).

Ltac2 rec reflect_term (ctx : constr list) (t : term) : constr :=
  match t with
  | Var n => List.nth ctx n
  | Val v => v
  | Binop op a b =>
      let ra := reflect_term ctx a in
      let rb := reflect_term ctx b in
      constr:(bop.eval $op $ra $rb)
  | Unop op a =>
      let ra := reflect_term ctx a in
      constr:(uop.eval $op $ra)
  | Tuple e =>
      let vs := reflect_env ctx e in
      constr:(envrec.of_env _ $vs)
  | Union u k a =>
      let v := reflect_term ctx a in
      constr:(unionv_fold $u (existT $k $v))
  | Record r e =>
      let vs := reflect_env ctx e in
      constr:(recordv_fold $r $vs)
  end

with reflect_env (ctx : constr list) (e : eenv) : constr :=
  match e with
  | EnvNil b =>
      let d := val_dom b in
      constr:(@env.nil $b $d)
  | EnvSnoc b bb t rest =>
      let d := val_dom b in
      let vs := reflect_env ctx rest in
      let v := reflect_term ctx t in
      constr:(@env.snoc $b $d _ $vs $bb $v)
  end.

Ltac2 rec reflect_formula (ctx : constr list) (f : formula) : constr :=
  match f with
  | User p e =>
      let vs := reflect_env ctx e in
      constr:(env.uncurry (𝑷_inst $p) $vs)
  | Bool t => let rt := reflect_term ctx t in constr:($rt = true)
  | Relop op a b =>
      let ra := reflect_term ctx a in
      let rb := reflect_term ctx b in
      constr:(bop.eval_relop_prop $op $ra $rb)
  | FTrue => constr:(True)
  | FFalse => constr:(False)
  | And a b =>
      let ra := reflect_formula ctx a in
      let rb := reflect_formula ctx b in
      constr:($ra /\ $rb)
  | Or a b =>
      let ra := reflect_formula ctx a in
      let rb := reflect_formula ctx b in
      constr:($ra \/ $rb)
  end.

Ltac2 rec reflect_sp (ctx : constr list) (sp : symprop) : constr :=
  match sp with
  | AngelicBin a b =>
      let refla := reflect_sp ctx a in
      let reflb := reflect_sp ctx b in
      constr:($refla \/ $reflb)
  | DemonicBin a b =>
      let refla := reflect_sp ctx a in
      let reflb := reflect_sp ctx b in
      constr:($refla /\ $reflb)
  | Error => constr:(False)
  | Block => constr:(True)
  | AssertK f k =>
      let reflf := reflect_formula ctx f in
      let reflk := reflect_sp ctx k in
      constr:($reflf /\ $reflk)
  | AssumeK f k =>
      let reflf := reflect_formula ctx f in
      let reflk := reflect_sp ctx k in
      constr:(forall _ : $reflf, $reflk)
  | Angelic name lt k =>
      let lam := with_var name lt (fun x => reflect_sp (x :: ctx) k) in
      constr:(@ex (Val $lt) $lam)
  | Demonic name lt k =>
      let lam := with_var name lt (fun x => reflect_sp (x :: ctx) k) in
      match Constr.Unsafe.kind lam with
      | Constr.Unsafe.Lambda b c => Constr.Unsafe.make (Constr.Unsafe.Prod b c)
      | _ => Control.throw (Tactic_failure (Some (fprintf "reflect_sp: expected a lambda but got '%t'" lam)))
      end
  | AssertVarEq n t k =>
      (* the variable n is replaced by the term t in the continuation *)
      let ctx' := list_remove ctx n in
      let x := List.nth ctx n in
      let rt := reflect_term ctx' t in
      let rk := reflect_sp ctx' k in
      constr:($x = $rt /\ $rk)
  | AssumeVarEq n t k =>
      let ctx' := list_remove ctx n in
      let x := List.nth ctx n in
      let rt := reflect_term ctx' t in
      let rk := reflect_sp ctx' k in
      constr:(forall _ : ($x = $rt), $rk)
  end.

(* ------------------------------------------------------------------------ *)
(* Tactic                                                                    *)
(* ------------------------------------------------------------------------ *)

(* Reify the erased symbolic proposition of the goal and replace the goal
   with the reflected Prop (checked by conversion). *)
Ltac2 reify_vc_goal () :=
  match! goal with
  | [ |- VerificationConditionWithErasure ?p ] =>
      let r := reflect_sp [] (reify_sp p) in
      constructor; change $r
  end.

(* The Ltac1 entry point. Control.enter is needed for this to work with all:
   and ; on multiple goals. *)
Ltac reify_vc := ltac2:(Control.enter reify_vc_goal).

Module Tests.
  (* Tests: reify_vc succeeds iff the reflected Prop is convertible to the
     goal, and the variables keep (freshened) names. *)
  Ltac2 has_hyps (ids : ident list) : unit :=
    List.iter (fun i => let _ := Control.hyp i in ()) ids.

  Goal VerificationConditionWithErasure
    (edemonicv (MkB "y" ty.bool)
       (eassumek (eformula_bool (@eterm_var "y" ty.bool 0)) eblock)).
  Proof. reify_vc. intros. ltac2:(has_hyps [@y]). Abort.

  (* "y.1" is not an identifier; the suffix is dropped. *)
  Goal VerificationConditionWithErasure
    (eangelicv (MkB "y.1" ty.bool)
       (eassertk (eformula_bool (@eterm_var "y.1" ty.bool 0)) eblock)).
  Proof. reify_vc. intros. ltac2:(has_hyps []). Abort.

  Goal VerificationConditionWithErasure
    (edemonicv (MkB "z" ty.bool) (edemonicv (MkB "y" ty.bool)
       (eassume_vareq "z" 1 (@eterm_var "y" ty.bool 0) eblock))).
  Proof. reify_vc. intros. ltac2:(has_hyps [@z; @y]). Abort.

  (* Invalid or reserved names are still accepted. *)
  Goal VerificationConditionWithErasure
    (edemonic_binary eblock
       (eangelicv (MkB "1x" ty.bool) (eangelicv (MkB "fun" ty.bool) eblock))).
  Proof. reify_vc. Abort.

  Goal VerificationConditionWithErasure
    (edemonicv (MkB "a" ty.bool)
       (eassumek
          (eformula_bool
             (eterm_binop bop.or
                (eterm_unop uop.not (@eterm_var "a" ty.bool 0))
                (eterm_val ty.bool true)))
          eblock)).
  Proof. reify_vc. intros. ltac2:(has_hyps [@a]). Abort.

  (* Clashing names are freshened: "L", "L.1" and "L.2" all start from L. *)
  Goal VerificationConditionWithErasure
    (edemonicv (MkB "L" ty.bool) (edemonicv (MkB "L.1" ty.bool)
       (edemonicv (MkB "L.2" ty.bool)
          (eassumek
             (eformula_bool
                (eterm_binop bop.or
                   (@eterm_var "L" ty.bool 2) (@eterm_var "L.2" ty.bool 0)))
             eblock)))).
  Proof. reify_vc. intros. ltac2:(has_hyps [@L; @L1]). Abort.
End Tests.
