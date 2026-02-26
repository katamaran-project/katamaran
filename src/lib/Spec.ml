open Ascii
open Base1
open BinInt
open BinNat
open BinNums
open BinOps
open Bitvector
open Context
open Contracts
open Datatypes
open Environment
open IrisInstance
open Machine
open Nat
open Prelude
open Sig
open String
open SymbolicExecutor
open TypeDecl
open UnOps
open Variables

type __ = Obj.t

module RiscvPmpBlockVerifFailLogic =
 struct
  (** val fail_rule_pre : bool **)

  let fail_rule_pre =
    Coq_false
 end

module RiscvPmpBlockVerifSpec =
 struct
  type coq_SepContractEnv =
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> RiscvPmpProgram.coq_Fun ->
    RiscvPmpSignature.coq_SepContract option

  type coq_SepContractEnvEx =
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    Coq_ty.coq_Ty -> RiscvPmpProgram.coq_FunX ->
    RiscvPmpSignature.coq_SepContract

  type coq_LemmaEnv =
    (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpProgram.coq_Lem -> RiscvPmpSignature.coq_Lemma

  type coq_SepContractFun = RiscvPmpSignature.coq_SepContract

  type coq_SepContractFunX = RiscvPmpSignature.coq_SepContract

  type coq_SepLemma = RiscvPmpSignature.coq_Lemma

  (** val term_eqb :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term **)

  let term_eqb _ e1 e2 =
    RiscvPmpBase.Coq_term_binop (RiscvPmpBase.ty_regno,
      RiscvPmpBase.ty_regno, Coq_ty.Coq_bool, (Coq_bop.Coq_relop
      (RiscvPmpBase.ty_regno, (Coq_bop.Coq_eq RiscvPmpBase.ty_regno))), e1,
      e2)

  (** val z_term :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> coq_Z
      -> RiscvPmpBase.coq_Term **)

  let z_term _ =
    Obj.magic (fun x -> RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int, x))

  (** val sep_contract_logvars :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx **)

  let sep_contract_logvars _UU0394_ _UU03a3_ =
    Coq_ctx.cat
      (Coq_ctx.map (fun pat ->
        let x = pat.Binding.name in
        let _UU03c3_ = pat.Binding.coq_type in
        { Binding.name = x; Binding.coq_type = _UU03c3_ }) _UU0394_)
      _UU03a3_

  (** val create_localstore :
      (coq_PVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_SStore **)

  let create_localstore _UU0394_ _UU03a3_ =
    Coq_env.tabulate _UU0394_ (fun pat ->
      let x = pat.Binding.name in
      let _UU03c3_ = pat.Binding.coq_type in
      (fun xIn -> RiscvPmpBase.Coq_term_var (x, _UU03c3_,
      (Coq_ctx.in_cat_left { Binding.name = x; Binding.coq_type = _UU03c3_ }
        (Coq_ctx.map (fun pat0 -> { Binding.name = pat0.Binding.name;
          Binding.coq_type = pat0.Binding.coq_type }) _UU0394_)
        _UU03a3_
        (Coq_ctx.in_map (fun pat0 ->
          let y = pat0.Binding.name in
          let _UU03c4_ = pat0.Binding.coq_type in
          { Binding.name = y; Binding.coq_type = _UU03c4_ }) { Binding.name =
          x; Binding.coq_type = _UU03c3_ } _UU0394_ xIn)))))

  (** val asn_exists :
      (string, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx -> (string,
      Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpSignature.Coq_asn.coq_Assertion ->
      RiscvPmpSignature.Coq_asn.coq_Assertion **)

  let rec asn_exists _UU03a3_ = function
  | Coq_ctx.Coq_nil -> (fun asn -> asn)
  | Coq_ctx.Coq_snoc (_UU0393_0, b) ->
    let x = b.Binding.name in
    let _UU03c4_ = b.Binding.coq_type in
    (fun asn ->
    asn_exists _UU03a3_ _UU0393_0 (RiscvPmpSignature.Coq_asn.Coq_exist
      ((Obj.magic x), _UU03c4_, asn)))

  (** val asn_with_reg :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> (RiscvPmpBase.coq_Reg ->
      RiscvPmpSignature.Coq_asn.coq_Assertion) ->
      RiscvPmpSignature.Coq_asn.coq_Assertion ->
      RiscvPmpSignature.Coq_asn.coq_Assertion **)

  let asn_with_reg _UU03a3_ r asn asn_default =
    RiscvPmpSignature.Coq_asn.match_bool _UU03a3_
      (term_eqb _UU03a3_ r (RiscvPmpBase.Coq_term_val (RiscvPmpBase.ty_regno,
        (Obj.magic Coq_bv.of_N (S (S (S (S (S O))))) N0))))
      asn_default
      (RiscvPmpSignature.Coq_asn.match_bool _UU03a3_
        (term_eqb _UU03a3_ r (RiscvPmpBase.Coq_term_val
          (RiscvPmpBase.ty_regno,
          (Obj.magic Coq_bv.of_N (S (S (S (S (S O))))) (Npos Coq_xH)))))
        (asn RiscvPmpBase.Coq_x1)
        (RiscvPmpSignature.Coq_asn.match_bool _UU03a3_
          (term_eqb _UU03a3_ r (RiscvPmpBase.Coq_term_val
            (RiscvPmpBase.ty_regno,
            (Obj.magic Coq_bv.of_N (S (S (S (S (S O))))) (Npos (Coq_xO
              Coq_xH))))))
          (asn RiscvPmpBase.Coq_x2)
          (RiscvPmpSignature.Coq_asn.match_bool _UU03a3_
            (term_eqb _UU03a3_ r (RiscvPmpBase.Coq_term_val
              (RiscvPmpBase.ty_regno,
              (Obj.magic Coq_bv.of_N (S (S (S (S (S O))))) (Npos (Coq_xI
                Coq_xH))))))
            (asn RiscvPmpBase.Coq_x3)
            (RiscvPmpSignature.Coq_asn.match_bool _UU03a3_
              (term_eqb _UU03a3_ r (RiscvPmpBase.Coq_term_val
                (RiscvPmpBase.ty_regno,
                (Obj.magic Coq_bv.of_N (S (S (S (S (S O))))) (Npos (Coq_xO
                  (Coq_xO Coq_xH)))))))
              (asn RiscvPmpBase.Coq_x4)
              (RiscvPmpSignature.Coq_asn.match_bool _UU03a3_
                (term_eqb _UU03a3_ r (RiscvPmpBase.Coq_term_val
                  (RiscvPmpBase.ty_regno,
                  (Obj.magic Coq_bv.of_N (S (S (S (S (S O))))) (Npos (Coq_xI
                    (Coq_xO Coq_xH)))))))
                (asn RiscvPmpBase.Coq_x5)
                (RiscvPmpSignature.Coq_asn.match_bool _UU03a3_
                  (term_eqb _UU03a3_ r (RiscvPmpBase.Coq_term_val
                    (RiscvPmpBase.ty_regno,
                    (Obj.magic Coq_bv.of_N (S (S (S (S (S O))))) (Npos
                      (Coq_xO (Coq_xI Coq_xH)))))))
                  (asn RiscvPmpBase.Coq_x6)
                  (RiscvPmpSignature.Coq_asn.match_bool _UU03a3_
                    (term_eqb _UU03a3_ r (RiscvPmpBase.Coq_term_val
                      (RiscvPmpBase.ty_regno,
                      (Obj.magic Coq_bv.of_N (S (S (S (S (S O))))) (Npos
                        (Coq_xI (Coq_xI Coq_xH)))))))
                    (asn RiscvPmpBase.Coq_x7)
                    (RiscvPmpSignature.Coq_asn.match_bool _UU03a3_
                      (term_eqb _UU03a3_ r (RiscvPmpBase.Coq_term_val
                        (RiscvPmpBase.ty_regno,
                        (Obj.magic Coq_bv.of_N (S (S (S (S (S O))))) (Npos
                          (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))))
                      (asn RiscvPmpBase.Coq_x8)
                      (RiscvPmpSignature.Coq_asn.match_bool _UU03a3_
                        (term_eqb _UU03a3_ r (RiscvPmpBase.Coq_term_val
                          (RiscvPmpBase.ty_regno,
                          (Obj.magic Coq_bv.of_N (S (S (S (S (S O))))) (Npos
                            (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))))
                        (asn RiscvPmpBase.Coq_x9)
                        (RiscvPmpSignature.Coq_asn.match_bool _UU03a3_
                          (term_eqb _UU03a3_ r (RiscvPmpBase.Coq_term_val
                            (RiscvPmpBase.ty_regno,
                            (Obj.magic Coq_bv.of_N (S (S (S (S (S O)))))
                              (Npos (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))))
                          (asn RiscvPmpBase.Coq_x10)
                          (RiscvPmpSignature.Coq_asn.match_bool _UU03a3_
                            (term_eqb _UU03a3_ r (RiscvPmpBase.Coq_term_val
                              (RiscvPmpBase.ty_regno,
                              (Obj.magic Coq_bv.of_N (S (S (S (S (S O)))))
                                (Npos (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))))
                            (asn RiscvPmpBase.Coq_x11)
                            (RiscvPmpSignature.Coq_asn.match_bool _UU03a3_
                              (term_eqb _UU03a3_ r (RiscvPmpBase.Coq_term_val
                                (RiscvPmpBase.ty_regno,
                                (Obj.magic Coq_bv.of_N (S (S (S (S (S O)))))
                                  (Npos (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))))
                              (asn RiscvPmpBase.Coq_x12)
                              (RiscvPmpSignature.Coq_asn.match_bool _UU03a3_
                                (term_eqb _UU03a3_ r
                                  (RiscvPmpBase.Coq_term_val
                                  (RiscvPmpBase.ty_regno,
                                  (Obj.magic Coq_bv.of_N (S (S (S (S (S
                                    O))))) (Npos (Coq_xI (Coq_xO (Coq_xI
                                    Coq_xH))))))))
                                (asn RiscvPmpBase.Coq_x13)
                                (RiscvPmpSignature.Coq_asn.match_bool
                                  _UU03a3_
                                  (term_eqb _UU03a3_ r
                                    (RiscvPmpBase.Coq_term_val
                                    (RiscvPmpBase.ty_regno,
                                    (Obj.magic Coq_bv.of_N (S (S (S (S (S
                                      O))))) (Npos (Coq_xO (Coq_xI (Coq_xI
                                      Coq_xH))))))))
                                  (asn RiscvPmpBase.Coq_x14)
                                  (RiscvPmpSignature.Coq_asn.match_bool
                                    _UU03a3_
                                    (term_eqb _UU03a3_ r
                                      (RiscvPmpBase.Coq_term_val
                                      (RiscvPmpBase.ty_regno,
                                      (Obj.magic Coq_bv.of_N (S (S (S (S (S
                                        O))))) (Npos (Coq_xI (Coq_xI (Coq_xI
                                        Coq_xH))))))))
                                    (asn RiscvPmpBase.Coq_x15)
                                    (RiscvPmpSignature.Coq_asn.match_bool
                                      _UU03a3_
                                      (term_eqb _UU03a3_ r
                                        (RiscvPmpBase.Coq_term_val
                                        (RiscvPmpBase.ty_regno,
                                        (Obj.magic Coq_bv.of_N (S (S (S (S (S
                                          O))))) (Npos (Coq_xO (Coq_xO
                                          (Coq_xO (Coq_xO Coq_xH)))))))))
                                      (asn RiscvPmpBase.Coq_x16)
                                      (RiscvPmpSignature.Coq_asn.match_bool
                                        _UU03a3_
                                        (term_eqb _UU03a3_ r
                                          (RiscvPmpBase.Coq_term_val
                                          (RiscvPmpBase.ty_regno,
                                          (Obj.magic Coq_bv.of_N (S (S (S (S
                                            (S O))))) (Npos (Coq_xI (Coq_xO
                                            (Coq_xO (Coq_xO Coq_xH)))))))))
                                        (asn RiscvPmpBase.Coq_x17)
                                        (RiscvPmpSignature.Coq_asn.match_bool
                                          _UU03a3_
                                          (term_eqb _UU03a3_ r
                                            (RiscvPmpBase.Coq_term_val
                                            (RiscvPmpBase.ty_regno,
                                            (Obj.magic Coq_bv.of_N (S (S (S
                                              (S (S O))))) (Npos (Coq_xO
                                              (Coq_xI (Coq_xO (Coq_xO
                                              Coq_xH)))))))))
                                          (asn RiscvPmpBase.Coq_x18)
                                          (RiscvPmpSignature.Coq_asn.match_bool
                                            _UU03a3_
                                            (term_eqb _UU03a3_ r
                                              (RiscvPmpBase.Coq_term_val
                                              (RiscvPmpBase.ty_regno,
                                              (Obj.magic Coq_bv.of_N (S (S (S
                                                (S (S O))))) (Npos (Coq_xI
                                                (Coq_xI (Coq_xO (Coq_xO
                                                Coq_xH)))))))))
                                            (asn RiscvPmpBase.Coq_x19)
                                            (RiscvPmpSignature.Coq_asn.match_bool
                                              _UU03a3_
                                              (term_eqb _UU03a3_ r
                                                (RiscvPmpBase.Coq_term_val
                                                (RiscvPmpBase.ty_regno,
                                                (Obj.magic Coq_bv.of_N (S (S
                                                  (S (S (S O))))) (Npos
                                                  (Coq_xO (Coq_xO (Coq_xI
                                                  (Coq_xO Coq_xH)))))))))
                                              (asn RiscvPmpBase.Coq_x20)
                                              (RiscvPmpSignature.Coq_asn.match_bool
                                                _UU03a3_
                                                (term_eqb _UU03a3_ r
                                                  (RiscvPmpBase.Coq_term_val
                                                  (RiscvPmpBase.ty_regno,
                                                  (Obj.magic Coq_bv.of_N (S
                                                    (S (S (S (S O))))) (Npos
                                                    (Coq_xI (Coq_xO (Coq_xI
                                                    (Coq_xO Coq_xH)))))))))
                                                (asn RiscvPmpBase.Coq_x21)
                                                (RiscvPmpSignature.Coq_asn.match_bool
                                                  _UU03a3_
                                                  (term_eqb _UU03a3_ r
                                                    (RiscvPmpBase.Coq_term_val
                                                    (RiscvPmpBase.ty_regno,
                                                    (Obj.magic Coq_bv.of_N (S
                                                      (S (S (S (S O)))))
                                                      (Npos (Coq_xO (Coq_xI
                                                      (Coq_xI (Coq_xO
                                                      Coq_xH)))))))))
                                                  (asn RiscvPmpBase.Coq_x22)
                                                  (RiscvPmpSignature.Coq_asn.match_bool
                                                    _UU03a3_
                                                    (term_eqb _UU03a3_ r
                                                      (RiscvPmpBase.Coq_term_val
                                                      (RiscvPmpBase.ty_regno,
                                                      (Obj.magic Coq_bv.of_N
                                                        (S (S (S (S (S O)))))
                                                        (Npos (Coq_xI (Coq_xI
                                                        (Coq_xI (Coq_xO
                                                        Coq_xH)))))))))
                                                    (asn RiscvPmpBase.Coq_x23)
                                                    (RiscvPmpSignature.Coq_asn.match_bool
                                                      _UU03a3_
                                                      (term_eqb _UU03a3_ r
                                                        (RiscvPmpBase.Coq_term_val
                                                        (RiscvPmpBase.ty_regno,
                                                        (Obj.magic
                                                          Coq_bv.of_N (S (S
                                                          (S (S (S O)))))
                                                          (Npos (Coq_xO
                                                          (Coq_xO (Coq_xO
                                                          (Coq_xI Coq_xH)))))))))
                                                      (asn
                                                        RiscvPmpBase.Coq_x24)
                                                      (RiscvPmpSignature.Coq_asn.match_bool
                                                        _UU03a3_
                                                        (term_eqb _UU03a3_ r
                                                          (RiscvPmpBase.Coq_term_val
                                                          (RiscvPmpBase.ty_regno,
                                                          (Obj.magic
                                                            Coq_bv.of_N (S (S
                                                            (S (S (S O)))))
                                                            (Npos (Coq_xI
                                                            (Coq_xO (Coq_xO
                                                            (Coq_xI
                                                            Coq_xH)))))))))
                                                        (asn
                                                          RiscvPmpBase.Coq_x25)
                                                        (RiscvPmpSignature.Coq_asn.match_bool
                                                          _UU03a3_
                                                          (term_eqb _UU03a3_
                                                            r
                                                            (RiscvPmpBase.Coq_term_val
                                                            (RiscvPmpBase.ty_regno,
                                                            (Obj.magic
                                                              Coq_bv.of_N (S
                                                              (S (S (S (S
                                                              O))))) (Npos
                                                              (Coq_xO (Coq_xI
                                                              (Coq_xO (Coq_xI
                                                              Coq_xH)))))))))
                                                          (asn
                                                            RiscvPmpBase.Coq_x26)
                                                          (RiscvPmpSignature.Coq_asn.match_bool
                                                            _UU03a3_
                                                            (term_eqb
                                                              _UU03a3_ r
                                                              (RiscvPmpBase.Coq_term_val
                                                              (RiscvPmpBase.ty_regno,
                                                              (Obj.magic
                                                                Coq_bv.of_N
                                                                (S (S (S (S
                                                                (S O)))))
                                                                (Npos (Coq_xI
                                                                (Coq_xI
                                                                (Coq_xO
                                                                (Coq_xI
                                                                Coq_xH)))))))))
                                                            (asn
                                                              RiscvPmpBase.Coq_x27)
                                                            (RiscvPmpSignature.Coq_asn.match_bool
                                                              _UU03a3_
                                                              (term_eqb
                                                                _UU03a3_ r
                                                                (RiscvPmpBase.Coq_term_val
                                                                (RiscvPmpBase.ty_regno,
                                                                (Obj.magic
                                                                  Coq_bv.of_N
                                                                  (S (S (S (S
                                                                  (S O)))))
                                                                  (Npos
                                                                  (Coq_xO
                                                                  (Coq_xO
                                                                  (Coq_xI
                                                                  (Coq_xI
                                                                  Coq_xH)))))))))
                                                              (asn
                                                                RiscvPmpBase.Coq_x28)
                                                              (RiscvPmpSignature.Coq_asn.match_bool
                                                                _UU03a3_
                                                                (term_eqb
                                                                  _UU03a3_ r
                                                                  (RiscvPmpBase.Coq_term_val
                                                                  (RiscvPmpBase.ty_regno,
                                                                  (Obj.magic
                                                                    Coq_bv.of_N
                                                                    (S (S (S
                                                                    (S (S
                                                                    O)))))
                                                                    (Npos
                                                                    (Coq_xI
                                                                    (Coq_xO
                                                                    (Coq_xI
                                                                    (Coq_xI
                                                                    Coq_xH)))))))))
                                                                (asn
                                                                  RiscvPmpBase.Coq_x29)
                                                                (RiscvPmpSignature.Coq_asn.match_bool
                                                                  _UU03a3_
                                                                  (term_eqb
                                                                    _UU03a3_
                                                                    r
                                                                    (RiscvPmpBase.Coq_term_val
                                                                    (RiscvPmpBase.ty_regno,
                                                                    (Obj.magic
                                                                    Coq_bv.of_N
                                                                    (S (S (S
                                                                    (S (S
                                                                    O)))))
                                                                    (Npos
                                                                    (Coq_xO
                                                                    (Coq_xI
                                                                    (Coq_xI
                                                                    (Coq_xI
                                                                    Coq_xH)))))))))
                                                                  (asn
                                                                    RiscvPmpBase.Coq_x30)
                                                                  (RiscvPmpSignature.Coq_asn.match_bool
                                                                    _UU03a3_
                                                                    (term_eqb
                                                                    _UU03a3_
                                                                    r
                                                                    (RiscvPmpBase.Coq_term_val
                                                                    (RiscvPmpBase.ty_regno,
                                                                    (Obj.magic
                                                                    Coq_bv.of_N
                                                                    (S (S (S
                                                                    (S (S
                                                                    O)))))
                                                                    (Npos
                                                                    (Coq_xI
                                                                    (Coq_xI
                                                                    (Coq_xI
                                                                    (Coq_xI
                                                                    Coq_xH)))))))))
                                                                    (asn
                                                                    RiscvPmpBase.Coq_x31)
                                                                    (RiscvPmpSignature.Coq_asn.Coq_formula
                                                                    (RiscvPmpSignature.Coq_formula_bool
                                                                    (RiscvPmpBase.Coq_term_val
                                                                    (Coq_ty.Coq_bool,
                                                                    (Obj.magic
                                                                    Coq_false))))))))))))))))))))))))))))))))))))

  (** val asn_reg_ptsto :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpBase.coq_Term -> RiscvPmpBase.coq_Term ->
      RiscvPmpSignature.Coq_asn.coq_Assertion **)

  let asn_reg_ptsto _UU03a3_ r w =
    asn_with_reg _UU03a3_ r (fun r0 -> RiscvPmpSignature.Coq_asn.Coq_chunk
      (RiscvPmpSignature.Coq_chunk_ptsreg (RiscvPmpBase.ty_xlenbits, r0, w)))
      (RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop (RiscvPmpBase.ty_word,
      (Coq_bop.Coq_eq RiscvPmpBase.ty_word), w, (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_word, (Obj.magic Coq_bv.zero word))))))

  (** val sep_contract_rX : RiscvPmpSpecification.coq_SepContractFun **)

  let sep_contract_rX =
    { RiscvPmpSignature.sep_contract_logic_variables = (Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))));
      Binding.coq_type = RiscvPmpBase.ty_regno })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_word }));
      RiscvPmpSignature.sep_contract_localstore = (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))));
      Binding.coq_type = RiscvPmpBase.ty_regno }, (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_true, Coq_false)), EmptyString))))),
      RiscvPmpBase.ty_regno, (S O)))));
      RiscvPmpSignature.sep_contract_precondition =
      (asn_reg_ptsto (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
        { Binding.name =
        (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false,
          Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
          Coq_true, Coq_true, Coq_false)), EmptyString)))));
        Binding.coq_type = RiscvPmpBase.ty_regno })), { Binding.name =
        (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
          Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
        Binding.coq_type = RiscvPmpBase.ty_word }))
        (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), EmptyString))))),
        RiscvPmpBase.ty_regno, (S O))) (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
        RiscvPmpBase.ty_word, O)));
      RiscvPmpSignature.sep_contract_result =
      (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_false)), EmptyString)))))))))))))))))));
      RiscvPmpSignature.sep_contract_postcondition =
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop ((Coq_ty.Coq_bvec (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S O))))))))))))))))))))))))))))))))), (Coq_bop.Coq_eq
      (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O)))))))))))))))))))))))))))))))))), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)),
         EmptyString))))))))))))))))))),
      (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))), O)), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
      (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))), (S O)))))),
      (asn_reg_ptsto (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
        (Coq_ctx.Coq_nil, { Binding.name =
        (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false,
          Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
          Coq_true, Coq_true, Coq_false)), EmptyString)))));
        Binding.coq_type = RiscvPmpBase.ty_regno })), { Binding.name =
        (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
          Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
        Binding.coq_type = RiscvPmpBase.ty_word })), { Binding.name =
        (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false,
          Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
          Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
          Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
          Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
          Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
          Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
          Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
          Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
          Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)), (String
          ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
          Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
          Coq_false, Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
          Coq_false)), EmptyString)))))))))))))))))));
        Binding.coq_type = RiscvPmpBase.ty_xlenbits }))
        (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), EmptyString))))),
        RiscvPmpBase.ty_regno, (S (S O)))) (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
        RiscvPmpBase.ty_word, (S O)))))) }

  (** val sep_contract_wX : RiscvPmpSpecification.coq_SepContractFun **)

  let sep_contract_wX =
    { RiscvPmpSignature.sep_contract_logic_variables = (Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))));
      Binding.coq_type = RiscvPmpBase.ty_regno })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits }));
      RiscvPmpSignature.sep_contract_localstore = (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false)), EmptyString)))));
      Binding.coq_type = RiscvPmpBase.ty_regno })), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false)), EmptyString)))));
      Binding.coq_type = RiscvPmpBase.ty_regno }, (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_true, Coq_false)), EmptyString))))),
      RiscvPmpBase.ty_regno, (S (S O)))))), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_xlenbits, (S O)))));
      RiscvPmpSignature.sep_contract_precondition =
      (asn_reg_ptsto (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
        (Coq_ctx.Coq_nil, { Binding.name =
        (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false,
          Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
          Coq_true, Coq_true, Coq_false)), EmptyString)))));
        Binding.coq_type = RiscvPmpBase.ty_regno })), { Binding.name =
        (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_false,
          Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
        Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
        (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
          Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
        Binding.coq_type = RiscvPmpBase.ty_xlenbits }))
        (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), EmptyString))))),
        RiscvPmpBase.ty_regno, (S (S O)))) (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
        RiscvPmpBase.ty_word, O)));
      RiscvPmpSignature.sep_contract_result =
      (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_false)), EmptyString)))))))))))))))))));
      RiscvPmpSignature.sep_contract_postcondition =
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop (Coq_ty.Coq_unit, (Coq_bop.Coq_eq
      Coq_ty.Coq_unit), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)),
         EmptyString))))))))))))))))))),
      Coq_ty.Coq_unit, O)), (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_unit,
      (Obj.magic Coq_tt)))))),
      (RiscvPmpSignature.Coq_asn.match_bool (Coq_ctx.Coq_snoc
        ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
        (Coq_ctx.Coq_nil, { Binding.name =
        (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false,
          Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
          Coq_true, Coq_true, Coq_false)), EmptyString)))));
        Binding.coq_type = RiscvPmpBase.ty_regno })), { Binding.name =
        (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_false,
          Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
        Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
        (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
          Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
        Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
        (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false,
          Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
          Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
          Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
          Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
          Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
          Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
          Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
          Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
          Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
          Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
          Coq_false, Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
          Coq_false)), EmptyString)))))))))))))))))));
        Binding.coq_type = Coq_ty.Coq_unit }))
        (term_eqb (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
          ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
          (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString)))));
          Binding.coq_type = RiscvPmpBase.ty_regno })), { Binding.name =
          (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            EmptyString)));
          Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
          (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            EmptyString)));
          Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
          (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_false)), EmptyString)))))))))))))))))));
          Binding.coq_type = Coq_ty.Coq_unit })) (RiscvPmpBase.Coq_term_var
          ((Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false,
             Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
             ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
             Coq_true, Coq_true, Coq_false)), EmptyString))))),
          RiscvPmpBase.ty_regno, (S (S (S O))))) (RiscvPmpBase.Coq_term_val
          (RiscvPmpBase.ty_regno, (Obj.magic N0))))
        (asn_reg_ptsto (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
          ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
          { Binding.name =
          (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString)))));
          Binding.coq_type = RiscvPmpBase.ty_regno })), { Binding.name =
          (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            EmptyString)));
          Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
          (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            EmptyString)));
          Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
          (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_false)), EmptyString)))))))))))))))))));
          Binding.coq_type = Coq_ty.Coq_unit })) (RiscvPmpBase.Coq_term_var
          ((Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false,
             Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
             ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
             Coq_true, Coq_true, Coq_false)), EmptyString))))),
          RiscvPmpBase.ty_regno, (S (S (S O))))) (RiscvPmpBase.Coq_term_val
          (RiscvPmpBase.ty_word, (Obj.magic Coq_bv.zero word))))
        (asn_reg_ptsto (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
          ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
          { Binding.name =
          (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString)))));
          Binding.coq_type = RiscvPmpBase.ty_regno })), { Binding.name =
          (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            EmptyString)));
          Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
          (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            EmptyString)));
          Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
          (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
            Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
            Coq_false)), EmptyString)))))))))))))))))));
          Binding.coq_type = Coq_ty.Coq_unit })) (RiscvPmpBase.Coq_term_var
          ((Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false,
             Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
             ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
             Coq_true, Coq_true, Coq_false)), EmptyString))))),
          RiscvPmpBase.ty_regno, (S (S (S O))))) (RiscvPmpBase.Coq_term_var
          ((Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_true,
             Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
             EmptyString))),
          RiscvPmpBase.ty_word, (S (S O)))))))) }

  (** val sep_contract_fetch_instr :
      RiscvPmpSpecification.coq_SepContractFun **)

  let sep_contract_fetch_instr =
    { RiscvPmpSignature.sep_contract_logic_variables = (Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_ast })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), EmptyString)))))))))))))));
      Binding.coq_type = (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry) }));
      RiscvPmpSignature.sep_contract_localstore = Coq_env.Coq_nil;
      RiscvPmpSignature.sep_contract_precondition =
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_chunk
      (RiscvPmpSignature.Coq_chunk_ptsreg (RiscvPmpBase.ty_xlenbits,
      RiscvPmpBase.Coq_pc, (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_xlenbits, (S (S O))))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
      (Coq_ptstoinstr, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
      Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits, (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_xlenbits, (S (S O)))))), RiscvPmpBase.ty_ast,
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_ast, (S O)))))))), (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop (Coq_ty.Coq_int, Coq_bop.Coq_le,
      (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int,
      (Obj.magic Z.of_N minAddr))), (RiscvPmpBase.Coq_term_unop
      ((Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))), Coq_ty.Coq_int,
      (Coq_uop.Coq_unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))),
      (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))), (S (S O))))))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop (Coq_ty.Coq_int, Coq_bop.Coq_le,
      (RiscvPmpBase.Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int,
      Coq_ty.Coq_int, Coq_bop.Coq_plus, (RiscvPmpBase.Coq_term_unop
      ((Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))), Coq_ty.Coq_int,
      (Coq_uop.Coq_unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))),
      (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))), (S (S O)))))),
      (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int,
      (Obj.magic Z.of_nat bytes_per_instr))))), (RiscvPmpBase.Coq_term_val
      (Coq_ty.Coq_int, (Obj.magic Z.of_N maxAddr)))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_chunk
      (RiscvPmpSignature.Coq_chunk_ptsreg (RiscvPmpBase.ty_privilege,
      RiscvPmpBase.Coq_cur_privilege, (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_privilege, (Obj.magic Machine)))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
      (Coq_pmp_entries, (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))))))),
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), O))))))),
      (RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_user (Coq_pmp_access, (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
      RiscvPmpBase.ty_word)), (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry))),
      RiscvPmpBase.ty_privilege)), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      RiscvPmpBase.ty_xlenbits)), RiscvPmpBase.ty_word)), (Coq_ty.Coq_list
      RiscvPmpBase.ty_pmpentry))), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
      RiscvPmpBase.ty_word)), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_xlenbits, (S (S O)))))), RiscvPmpBase.ty_word,
      (RiscvPmpBase.Coq_term_val (RiscvPmpBase.ty_word,
      (Obj.magic bv_instrsize word))))), (Coq_ty.Coq_list
      RiscvPmpBase.ty_pmpentry), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))))))),
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), O)))),
      RiscvPmpBase.ty_privilege, (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_privilege, (Obj.magic Machine))))),
      RiscvPmpBase.ty_access_type, (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_access_type, (Obj.magic Execute))))))))))))))))))));
      RiscvPmpSignature.sep_contract_result =
      (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))))))))))))))))))))));
      RiscvPmpSignature.sep_contract_postcondition =
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_chunk
      (RiscvPmpSignature.Coq_chunk_ptsreg (RiscvPmpBase.ty_xlenbits,
      RiscvPmpBase.Coq_pc, (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_xlenbits, (S (S (S O)))))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
      (Coq_ptstoinstr, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
      Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits, (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_xlenbits, (S (S (S O))))))), RiscvPmpBase.ty_ast,
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_ast, (S (S O))))))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_exist
      ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
      (RiscvPmpBase.typedefkit.Coq_ty.unionk_ty (Obj.magic Coq_fetch_result)
        (Obj.magic KF_Base)),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop ((Coq_ty.Coq_union
      (Obj.magic Coq_fetch_result)), (Coq_bop.Coq_eq (Coq_ty.Coq_union
      (Obj.magic Coq_fetch_result))), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_true, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_true, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))))))))))))))))))))),
      (Coq_ty.Coq_union (Obj.magic Coq_fetch_result)), (S O))),
      (RiscvPmpBase.Coq_term_union ((Obj.magic Coq_fetch_result),
      (Obj.magic KF_Base), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
      (RiscvPmpBase.typedefkit.Coq_ty.unionk_ty (Obj.magic Coq_fetch_result)
        (Obj.magic KF_Base)),
      O))))))), (RiscvPmpSignature.Coq_asn.Coq_chunk
      (RiscvPmpSignature.Coq_chunk_user (Coq_encodes_instr, (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_word)),
      (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
      RiscvPmpBase.ty_word, (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_word, O)))), RiscvPmpBase.ty_ast,
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_ast, (S (S (S O)))))))))))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_chunk
      (RiscvPmpSignature.Coq_chunk_ptsreg (RiscvPmpBase.ty_privilege,
      RiscvPmpBase.Coq_cur_privilege, (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_privilege, (Obj.magic Machine)))))),
      (RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
      (Coq_pmp_entries, (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))))))),
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), (S O)))))))))))))))) }

  (** val sep_contract_checked_mem_read :
      nat -> RiscvPmpSpecification.coq_SepContractFun **)

  let sep_contract_checked_mem_read bytes =
    { RiscvPmpSignature.sep_contract_logic_variables = (Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))));
      Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))));
      Binding.coq_type = RiscvPmpBase.ty_access_type })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) }));
      RiscvPmpSignature.sep_contract_localstore = (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_access_type })), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_access_type },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))),
      RiscvPmpBase.ty_access_type, (S (S O)))))), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_xlenbits, (S O)))));
      RiscvPmpSignature.sep_contract_precondition =
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.match_bool (Coq_ctx.Coq_snoc
         ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
         (Coq_ctx.Coq_nil, { Binding.name =
         (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
           Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), EmptyString)))))));
         Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), EmptyString)))))));
         Binding.coq_type = RiscvPmpBase.ty_access_type })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), EmptyString)))))))))));
         Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
         Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) }))
         (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), EmptyString))))))),
         Coq_ty.Coq_bool, (S (S (S O)))))
         (RiscvPmpSignature.Coq_asn.Coq_chunk
         (RiscvPmpSignature.Coq_chunk_user ((Coq_ptstomem_readonly bytes),
         (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
         RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
         Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
         (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
         RiscvPmpBase.ty_xlenbits, (S O))))), (Coq_ty.Coq_bvec
         (mul bytes byte)), (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            EmptyString))),
         (Coq_ty.Coq_bvec (mul bytes byte)), O)))))))
         (RiscvPmpSignature.Coq_asn.Coq_chunk
         (RiscvPmpSignature.Coq_chunk_user ((Coq_ptstomem bytes),
         (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
         RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
         Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
         (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
         RiscvPmpBase.ty_xlenbits, (S O))))), (Coq_ty.Coq_bvec
         (mul bytes byte)), (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            EmptyString))),
         (Coq_ty.Coq_bvec (mul bytes byte)), O)))))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop (Coq_ty.Coq_int, Coq_bop.Coq_le,
      (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int,
      (Obj.magic Z.of_N minAddr))), (RiscvPmpBase.Coq_term_unop
      ((Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))), Coq_ty.Coq_int,
      (Coq_uop.Coq_unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))), (S O)))))))),
      (RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop (Coq_ty.Coq_int, Coq_bop.Coq_le,
      (RiscvPmpBase.Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int,
      Coq_ty.Coq_int, Coq_bop.Coq_plus, (RiscvPmpBase.Coq_term_unop
      ((Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))), Coq_ty.Coq_int,
      (Coq_uop.Coq_unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))), (S O))))),
      (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int,
      (Obj.magic Z.of_nat bytes))))), (RiscvPmpBase.Coq_term_val
      (Coq_ty.Coq_int, (Obj.magic Z.of_N maxAddr))))))))));
      RiscvPmpSignature.sep_contract_result =
      (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))))))))))))))))))))))))))));
      RiscvPmpSignature.sep_contract_postcondition =
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop ((Coq_ty.Coq_union
      (Obj.magic (Coq_memory_op_result bytes))), (Coq_bop.Coq_eq
      (Coq_ty.Coq_union (Obj.magic (Coq_memory_op_result bytes)))),
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_true, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))))))))))))))))))))))))))),
      (Coq_ty.Coq_union (Obj.magic (Coq_memory_op_result bytes))), O)),
      (RiscvPmpBase.Coq_term_union ((Obj.magic (Coq_memory_op_result bytes)),
      (Obj.magic KMemValue), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
      (RiscvPmpBase.typedefkit.Coq_ty.unionk_ty
        (Obj.magic (Coq_memory_op_result bytes)) (Obj.magic KMemValue)),
      (S O)))))))),
      (RiscvPmpSignature.Coq_asn.match_bool (Coq_ctx.Coq_snoc
        ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
        ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
        (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
          Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
          (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
          Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
          Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
          EmptyString)))))));
        Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
        (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true,
          Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
          Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
          Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
          Coq_false)), EmptyString)))))));
        Binding.coq_type = RiscvPmpBase.ty_access_type })), { Binding.name =
        (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
          Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
          Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
          Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
          Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
          Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
          Coq_true, Coq_true, Coq_false)), EmptyString)))))))))));
        Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
        (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
          Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
        Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) })),
        { Binding.name =
        (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false,
          Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
          Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
          Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
          Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
          Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
          Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
          Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
          Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
          Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
          Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
          Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
          Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
          Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
          Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
          Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
          Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
          Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
          Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
          Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
          Coq_false)), EmptyString)))))))))))))))))))))))))))))));
        Binding.coq_type = (RiscvPmpBase.ty_memory_op_result bytes) }))
        (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
           Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), EmptyString))))))),
        Coq_ty.Coq_bool, (S (S (S (S O))))))
        (RiscvPmpSignature.Coq_asn.Coq_chunk
        (RiscvPmpSignature.Coq_chunk_user ((Coq_ptstomem_readonly bytes),
        (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
        RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
        Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits, (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
        RiscvPmpBase.ty_xlenbits, (S (S O)))))), (Coq_ty.Coq_bvec
        (mul bytes byte)), (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
        (Coq_ty.Coq_bvec (mul bytes byte)), (S O))))))))
        (RiscvPmpSignature.Coq_asn.Coq_chunk
        (RiscvPmpSignature.Coq_chunk_user ((Coq_ptstomem bytes),
        (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
        RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
        Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits, (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
        RiscvPmpBase.ty_xlenbits, (S (S O)))))), (Coq_ty.Coq_bvec
        (mul bytes byte)), (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
        (Coq_ty.Coq_bvec (mul bytes byte)), (S O))))))))))) }

  (** val sep_contract_checked_mem_write :
      nat -> RiscvPmpSpecification.coq_SepContractFun **)

  let sep_contract_checked_mem_write bytes =
    { RiscvPmpSignature.sep_contract_logic_variables = (Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))));
      Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString)))))))));
      Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) }));
      RiscvPmpSignature.sep_contract_localstore = (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits })), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_xlenbits, (S O))))), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString)))))))));
      Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))))))))),
      (RiscvPmpBase.ty_bytes bytes), O))));
      RiscvPmpSignature.sep_contract_precondition =
      (RiscvPmpSignature.Coq_asn.match_bool (Coq_ctx.Coq_snoc
        ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
        { Binding.name =
        (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
          Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
          (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
          Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
          Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
          EmptyString)))))));
        Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
        (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
          Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
          Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
          Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
          Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
          Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
          Coq_true, Coq_true, Coq_false)), EmptyString)))))))))));
        Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
        (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true,
          Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
          Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
          Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
          Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
          Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
          EmptyString)))))))));
        Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) }))
        (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
           Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), EmptyString))))))),
        Coq_ty.Coq_bool, (S (S O)))) (RiscvPmpSignature.Coq_asn.Coq_sep
        ((RiscvPmpSignature.Coq_asn.Coq_formula
        (RiscvPmpSignature.Coq_formula_user ((Coq_in_mmio bytes),
        (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
        RiscvPmpBase.ty_xlenbits, (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
        RiscvPmpBase.ty_xlenbits, (S O)))))))),
        (RiscvPmpSignature.Coq_asn.Coq_sep
        ((RiscvPmpSignature.Coq_asn.Coq_formula
        (RiscvPmpSignature.Coq_formula_relop (Coq_ty.Coq_int, Coq_bop.Coq_lt,
        (RiscvPmpBase.Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int,
        Coq_ty.Coq_int, Coq_bop.Coq_plus, (RiscvPmpBase.Coq_term_unop
        ((Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))), Coq_ty.Coq_int,
        (Coq_uop.Coq_unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))), (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
        (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))), (S O))))),
        (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int,
        (Obj.magic Z.of_nat bytes))))), (RiscvPmpBase.Coq_term_val
        (Coq_ty.Coq_int,
        (Obj.magic Z.of_N (N.pow (Npos (Coq_xO Coq_xH)) (N.of_nat xlenbits)))))))),
        (RiscvPmpSignature.Coq_asn.Coq_sep
        ((RiscvPmpSignature.Coq_asn.Coq_chunk
        (RiscvPmpSignature.Coq_chunk_user ((Coq_inv_mmio bytes),
        Coq_env.Coq_nil))), (RiscvPmpSignature.Coq_asn.Coq_chunk
        (RiscvPmpSignature.Coq_chunk_user ((Coq_mmio_checked_write bytes),
        (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
        RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
        Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits, (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
        RiscvPmpBase.ty_xlenbits, (S O))))), (Coq_ty.Coq_bvec
        (mul bytes byte)), (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
           EmptyString))))))))),
        (Coq_ty.Coq_bvec (mul bytes byte)), O)))))))))))))
        (RiscvPmpSignature.Coq_asn.Coq_sep
        ((RiscvPmpSignature.Coq_asn.Coq_exist
        ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
        (Coq_ty.Coq_bvec (mul bytes byte)),
        (RiscvPmpSignature.Coq_asn.Coq_chunk
        (RiscvPmpSignature.Coq_chunk_user ((Coq_ptstomem bytes),
        (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
        RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
        Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits, (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
        RiscvPmpBase.ty_xlenbits, (S (S O)))))), (Coq_ty.Coq_bvec
        (mul bytes byte)), (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
        (Coq_ty.Coq_bvec (mul bytes byte)), O))))))))),
        (RiscvPmpSignature.Coq_asn.Coq_sep
        ((RiscvPmpSignature.Coq_asn.Coq_formula
        (RiscvPmpSignature.Coq_formula_relop (Coq_ty.Coq_int, Coq_bop.Coq_le,
        (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int,
        (Obj.magic Z.of_N minAddr))), (RiscvPmpBase.Coq_term_unop
        ((Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))), Coq_ty.Coq_int,
        (Coq_uop.Coq_unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))), (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
        (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))), (S O)))))))),
        (RiscvPmpSignature.Coq_asn.Coq_formula
        (RiscvPmpSignature.Coq_formula_relop (Coq_ty.Coq_int, Coq_bop.Coq_le,
        (RiscvPmpBase.Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int,
        Coq_ty.Coq_int, Coq_bop.Coq_plus, (RiscvPmpBase.Coq_term_unop
        ((Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))), Coq_ty.Coq_int,
        (Coq_uop.Coq_unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))), (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
        (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))), (S O))))),
        (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int,
        (Obj.magic Z.of_nat bytes))))), (RiscvPmpBase.Coq_term_val
        (Coq_ty.Coq_int, (Obj.magic Z.of_N maxAddr)))))))))));
      RiscvPmpSignature.sep_contract_result =
      (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true,
        Coq_true, Coq_false, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))))))))))))))))))))))))))))))))))))))))))))));
      RiscvPmpSignature.sep_contract_postcondition =
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop ((Coq_ty.Coq_union
      (Obj.magic (Coq_memory_op_result (S O)))), (Coq_bop.Coq_eq
      (Coq_ty.Coq_union (Obj.magic (Coq_memory_op_result (S O))))),
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_true, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_true, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
         Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))))))))))))))))))))))))))))))))))))))))))))),
      (Coq_ty.Coq_union (Obj.magic (Coq_memory_op_result (S O)))), O)),
      (RiscvPmpBase.Coq_term_union ((Obj.magic (Coq_memory_op_result (S O))),
      (Obj.magic KMemValue), (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_byte, (Obj.magic (Npos Coq_xH))))))))),
      (RiscvPmpSignature.Coq_asn.match_bool (Coq_ctx.Coq_snoc
        ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
        (Coq_ctx.Coq_nil, { Binding.name =
        (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
          Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
          (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
          Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
          Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
          EmptyString)))))));
        Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
        (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
          Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
          Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
          Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
          Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
          Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
          Coq_true, Coq_true, Coq_false)), EmptyString)))))))))));
        Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
        (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true,
          Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
          Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
          Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
          Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
          Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
          EmptyString)))))))));
        Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) })),
        { Binding.name =
        (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false,
          Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
          Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
          Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
          Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
          Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
          Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
          Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
          Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
          Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
          Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
          Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
          Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
          Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
          Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
          Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
          Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
          Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
          Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
          Coq_true, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
          Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
          Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
          Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
          Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
          Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
          Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
          Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
          Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
          Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
          Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
          Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
          Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
          Coq_false)),
          EmptyString)))))))))))))))))))))))))))))))))))))))))))))))));
        Binding.coq_type = (RiscvPmpBase.ty_memory_op_result (S O)) }))
        (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
           Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), EmptyString))))))),
        Coq_ty.Coq_bool, (S (S (S O)))))
        (RiscvPmpSignature.Coq_asn.Coq_formula
        (RiscvPmpSignature.Coq_formula_bool (RiscvPmpBase.Coq_term_val
        (Coq_ty.Coq_bool, (Obj.magic Coq_true)))))
        (RiscvPmpSignature.Coq_asn.Coq_chunk
        (RiscvPmpSignature.Coq_chunk_user ((Coq_ptstomem bytes),
        (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
        RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
        Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits, (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
        RiscvPmpBase.ty_xlenbits, (S (S O)))))), (Coq_ty.Coq_bvec
        (mul bytes byte)), (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
           EmptyString))))))))),
        (Coq_ty.Coq_bvec (mul bytes byte)), (S O))))))))))) }

  (** val sep_contract_pmpCheck :
      nat -> RiscvPmpSpecification.coq_SepContractFun **)

  let sep_contract_pmpCheck bytes =
    { RiscvPmpSignature.sep_contract_logic_variables = (Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), EmptyString)))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))));
      Binding.coq_type = RiscvPmpBase.ty_access_type })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), EmptyString)))))))));
      Binding.coq_type = RiscvPmpBase.ty_privilege })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), EmptyString)))))))))))))));
      Binding.coq_type = (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry) }));
      RiscvPmpSignature.sep_contract_localstore = (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), EmptyString)))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))));
      Binding.coq_type = RiscvPmpBase.ty_access_type })), (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), EmptyString)))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits })), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), EmptyString)))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))))))))),
      RiscvPmpBase.ty_xlenbits, (S (S (S O))))))), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))));
      Binding.coq_type = RiscvPmpBase.ty_access_type },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
         Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))),
      RiscvPmpBase.ty_access_type, (S (S O)))))), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), EmptyString)))))))));
      Binding.coq_type = RiscvPmpBase.ty_privilege },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))))),
      RiscvPmpBase.ty_privilege, (S O)))));
      RiscvPmpSignature.sep_contract_precondition =
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
      (Coq_pmp_entries, (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))))))),
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), O))))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop (RiscvPmpBase.ty_privilege,
      (Coq_bop.Coq_eq RiscvPmpBase.ty_privilege), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))))),
      RiscvPmpBase.ty_privilege, (S O))), (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_privilege, (Obj.magic Machine)))))),
      (RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_user (Coq_pmp_access, (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
      (Coq_ty.Coq_bvec xlenbits))), (Coq_ty.Coq_list
      RiscvPmpBase.ty_pmpentry))), RiscvPmpBase.ty_privilege)),
      (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
      (Coq_ty.Coq_bvec xlenbits))), (Coq_ty.Coq_list
      RiscvPmpBase.ty_pmpentry))), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
      (Coq_ty.Coq_bvec xlenbits))), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))))))))),
      RiscvPmpBase.ty_xlenbits, (S (S (S O))))))), (Coq_ty.Coq_bvec
      xlenbits), (RiscvPmpBase.Coq_term_unop (Coq_ty.Coq_int,
      (Coq_ty.Coq_bvec xlenbits), (Coq_uop.Coq_get_slice_int xlenbits),
      (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int,
      (Obj.magic Z.of_nat bytes))))))), (Coq_ty.Coq_list
      RiscvPmpBase.ty_pmpentry), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))))))),
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), O)))),
      RiscvPmpBase.ty_privilege, (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))))),
      RiscvPmpBase.ty_privilege, (S O))))), RiscvPmpBase.ty_access_type,
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
         Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))),
      RiscvPmpBase.ty_access_type, (S (S O)))))))))))));
      RiscvPmpSignature.sep_contract_result =
      (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_false)),
        EmptyString)))))))))))))))))))))))))))))));
      RiscvPmpSignature.sep_contract_postcondition =
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop ((Coq_ty.Coq_sum
      ((Coq_ty.Coq_union (Obj.magic Coq_exception_type)), Coq_ty.Coq_unit)),
      (Coq_bop.Coq_eq (Coq_ty.Coq_sum ((Coq_ty.Coq_union
      (Obj.magic Coq_exception_type)), Coq_ty.Coq_unit))),
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_true, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_true, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))))))))))))))))))))))))))),
      (Coq_ty.Coq_sum ((Coq_ty.Coq_union (Obj.magic Coq_exception_type)),
      Coq_ty.Coq_unit)), O)), (RiscvPmpBase.Coq_term_unop (Coq_ty.Coq_unit,
      (Coq_ty.Coq_sum ((Coq_ty.Coq_union (Obj.magic Coq_exception_type)),
      Coq_ty.Coq_unit)), (Coq_uop.Coq_inr ((Coq_ty.Coq_union
      (Obj.magic Coq_exception_type)), Coq_ty.Coq_unit)),
      (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_unit, (Obj.magic Coq_tt)))))))),
      (RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
      (Coq_pmp_entries, (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))))))),
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), (S O)))))))))) }

  (** val sep_contract_pmp_mem_read :
      nat -> RiscvPmpSpecification.coq_SepContractFun **)

  let sep_contract_pmp_mem_read bytes =
    { RiscvPmpSignature.sep_contract_logic_variables = (Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))));
      Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))));
      Binding.coq_type = RiscvPmpBase.ty_access_type })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), EmptyString)))))))))))))));
      Binding.coq_type = (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry) })),
      { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_privilege }));
      RiscvPmpSignature.sep_contract_localstore = (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_access_type })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_privilege })), (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_access_type })), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_access_type },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))),
      RiscvPmpBase.ty_access_type, (S (S (S (S O)))))))), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_privilege },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_privilege, O)))), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_xlenbits, (S (S (S O)))))));
      RiscvPmpSignature.sep_contract_precondition =
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.match_bool (Coq_ctx.Coq_snoc
         ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
         ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
         { Binding.name =
         (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
           Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), EmptyString)))))));
         Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), EmptyString)))))));
         Binding.coq_type = RiscvPmpBase.ty_access_type })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), EmptyString)))))))))));
         Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
           EmptyString)))))))))))))));
         Binding.coq_type = (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry) })),
         { Binding.name =
         (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
         Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) })),
         { Binding.name =
         (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
           Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString)));
         Binding.coq_type = RiscvPmpBase.ty_privilege }))
         (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), EmptyString))))))),
         Coq_ty.Coq_bool, (S (S (S (S (S O)))))))
         (RiscvPmpSignature.Coq_asn.Coq_chunk
         (RiscvPmpSignature.Coq_chunk_user ((Coq_ptstomem_readonly bytes),
         (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
         RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
         Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
         (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
         RiscvPmpBase.ty_xlenbits, (S (S (S O))))))), (Coq_ty.Coq_bvec
         (mul bytes byte)), (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            EmptyString))),
         (Coq_ty.Coq_bvec (mul bytes byte)), (S O))))))))
         (RiscvPmpSignature.Coq_asn.Coq_chunk
         (RiscvPmpSignature.Coq_chunk_user ((Coq_ptstomem bytes),
         (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
         RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
         Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
         (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
         RiscvPmpBase.ty_xlenbits, (S (S (S O))))))), (Coq_ty.Coq_bvec
         (mul bytes byte)), (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            EmptyString))),
         (Coq_ty.Coq_bvec (mul bytes byte)), (S O))))))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop (RiscvPmpBase.ty_privilege,
      (Coq_bop.Coq_eq RiscvPmpBase.ty_privilege), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_privilege, O)), (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_privilege, (Obj.magic Machine)))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop (Coq_ty.Coq_int, Coq_bop.Coq_le,
      (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int,
      (Obj.magic Z.of_N minAddr))), (RiscvPmpBase.Coq_term_unop
      ((Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))), Coq_ty.Coq_int,
      (Coq_uop.Coq_unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))), (S (S (S O)))))))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop (Coq_ty.Coq_int, Coq_bop.Coq_le,
      (RiscvPmpBase.Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int,
      Coq_ty.Coq_int, Coq_bop.Coq_plus, (RiscvPmpBase.Coq_term_unop
      ((Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))), Coq_ty.Coq_int,
      (Coq_uop.Coq_unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))), (S (S (S O))))))),
      (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int,
      (Obj.magic Z.of_nat bytes))))), (RiscvPmpBase.Coq_term_val
      (Coq_ty.Coq_int, (Obj.magic Z.of_N maxAddr)))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_chunk
      (RiscvPmpSignature.Coq_chunk_ptsreg (RiscvPmpBase.ty_privilege,
      RiscvPmpBase.Coq_cur_privilege, (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_privilege, O))))), (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
      (Coq_pmp_entries, (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))))))),
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), (S (S O))))))))),
      (RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_user (Coq_pmp_access, (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
      (Coq_ty.Coq_bvec xlenbits))), (Coq_ty.Coq_list
      RiscvPmpBase.ty_pmpentry))), RiscvPmpBase.ty_privilege)),
      (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
      (Coq_ty.Coq_bvec xlenbits))), (Coq_ty.Coq_list
      RiscvPmpBase.ty_pmpentry))), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
      (Coq_ty.Coq_bvec xlenbits))), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_xlenbits, (S (S (S O))))))), (Coq_ty.Coq_bvec
      xlenbits), (RiscvPmpBase.Coq_term_unop (Coq_ty.Coq_int,
      (Coq_ty.Coq_bvec xlenbits), (Coq_uop.Coq_get_slice_int xlenbits),
      (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int,
      (Obj.magic Z.of_nat bytes))))))), (Coq_ty.Coq_list
      RiscvPmpBase.ty_pmpentry), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))))))),
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), (S (S O)))))),
      RiscvPmpBase.ty_privilege, (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_privilege, O)))), RiscvPmpBase.ty_access_type,
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))),
      RiscvPmpBase.ty_access_type, (S (S (S (S O)))))))))))))))))))))));
      RiscvPmpSignature.sep_contract_result =
      (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))))))))))))))))))))))))))));
      RiscvPmpSignature.sep_contract_postcondition =
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop ((Coq_ty.Coq_union
      (Obj.magic (Coq_memory_op_result bytes))), (Coq_bop.Coq_eq
      (Coq_ty.Coq_union (Obj.magic (Coq_memory_op_result bytes)))),
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_true, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))))))))))))))))))))))))))),
      (Coq_ty.Coq_union (Obj.magic (Coq_memory_op_result bytes))), O)),
      (RiscvPmpBase.Coq_term_union ((Obj.magic (Coq_memory_op_result bytes)),
      (Obj.magic KMemValue), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
      (RiscvPmpBase.typedefkit.Coq_ty.unionk_ty
        (Obj.magic (Coq_memory_op_result bytes)) (Obj.magic KMemValue)),
      (S (S O))))))))), (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.match_bool (Coq_ctx.Coq_snoc
         ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
         ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
         (Coq_ctx.Coq_nil, { Binding.name =
         (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
           Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), EmptyString)))))));
         Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), EmptyString)))))));
         Binding.coq_type = RiscvPmpBase.ty_access_type })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), EmptyString)))))))))));
         Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
           EmptyString)))))))))))))));
         Binding.coq_type = (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry) })),
         { Binding.name =
         (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
         Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) })),
         { Binding.name =
         (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
           Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString)));
         Binding.coq_type = RiscvPmpBase.ty_privilege })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
           Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
           Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
           Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
           Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), EmptyString)))))))))))))))))))))))))))))));
         Binding.coq_type = (RiscvPmpBase.ty_memory_op_result bytes) }))
         (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), EmptyString))))))),
         Coq_ty.Coq_bool, (S (S (S (S (S (S O))))))))
         (RiscvPmpSignature.Coq_asn.Coq_chunk
         (RiscvPmpSignature.Coq_chunk_user ((Coq_ptstomem_readonly bytes),
         (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
         RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
         Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
         (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
         RiscvPmpBase.ty_xlenbits, (S (S (S (S O)))))))), (Coq_ty.Coq_bvec
         (mul bytes byte)), (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            EmptyString))),
         (Coq_ty.Coq_bvec (mul bytes byte)), (S (S O)))))))))
         (RiscvPmpSignature.Coq_asn.Coq_chunk
         (RiscvPmpSignature.Coq_chunk_user ((Coq_ptstomem bytes),
         (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
         RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
         Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
         (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
         RiscvPmpBase.ty_xlenbits, (S (S (S (S O)))))))), (Coq_ty.Coq_bvec
         (mul bytes byte)), (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            EmptyString))),
         (Coq_ty.Coq_bvec (mul bytes byte)), (S (S O)))))))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_chunk
      (RiscvPmpSignature.Coq_chunk_ptsreg (RiscvPmpBase.ty_privilege,
      RiscvPmpBase.Coq_cur_privilege, (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_privilege, (Obj.magic Machine)))))),
      (RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
      (Coq_pmp_entries, (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))))))),
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), (S (S (S O)))))))))))))))) }

  (** val sep_contract_pmp_mem_write :
      nat -> RiscvPmpSpecification.coq_SepContractFun **)

  let sep_contract_pmp_mem_write bytes =
    { RiscvPmpSignature.sep_contract_logic_variables = (Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))));
      Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString)))))))));
      Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))));
      Binding.coq_type = RiscvPmpBase.ty_access_type })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_privilege })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), EmptyString)))))))))))))));
      Binding.coq_type = (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry) }));
      RiscvPmpSignature.sep_contract_localstore = (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString)))))))));
      Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))));
      Binding.coq_type = RiscvPmpBase.ty_access_type })), (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString)))))))));
      Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) })), (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits })), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_xlenbits, (S (S (S (S O)))))))), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString)))))))));
      Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))))))))),
      (RiscvPmpBase.ty_bytes bytes), (S (S (S O))))))), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))));
      Binding.coq_type = RiscvPmpBase.ty_access_type },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))),
      RiscvPmpBase.ty_access_type, (S (S O)))))), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), EmptyString)))))))));
      Binding.coq_type = RiscvPmpBase.ty_privilege },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_privilege, (S O)))));
      RiscvPmpSignature.sep_contract_precondition =
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.match_bool (Coq_ctx.Coq_snoc
         ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
         ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
         { Binding.name =
         (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
           Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), EmptyString)))))));
         Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), EmptyString)))))))))));
         Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
           EmptyString)))))))));
         Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) })),
         { Binding.name =
         (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), EmptyString)))))));
         Binding.coq_type = RiscvPmpBase.ty_access_type })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
           Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString)));
         Binding.coq_type = RiscvPmpBase.ty_privilege })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
           EmptyString)))))))))))))));
         Binding.coq_type = (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry) }))
         (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), EmptyString))))))),
         Coq_ty.Coq_bool, (S (S (S (S (S O)))))))
         (RiscvPmpSignature.Coq_asn.Coq_sep
         ((RiscvPmpSignature.Coq_asn.Coq_formula
         (RiscvPmpSignature.Coq_formula_user ((Coq_in_mmio bytes),
         (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
         RiscvPmpBase.ty_xlenbits, (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
         RiscvPmpBase.ty_xlenbits, (S (S (S (S O))))))))))),
         (RiscvPmpSignature.Coq_asn.Coq_sep
         ((RiscvPmpSignature.Coq_asn.Coq_formula
         (RiscvPmpSignature.Coq_formula_relop (Coq_ty.Coq_int,
         Coq_bop.Coq_lt, (RiscvPmpBase.Coq_term_binop (Coq_ty.Coq_int,
         Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_bop.Coq_plus,
         (RiscvPmpBase.Coq_term_unop ((Coq_ty.Coq_bvec (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S O))))))))))))))))))))))))))))))))), Coq_ty.Coq_int,
         (Coq_uop.Coq_unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))), (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
         (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))), (S (S (S (S O)))))))),
         (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int,
         (Obj.magic Z.of_nat bytes))))), (RiscvPmpBase.Coq_term_val
         (Coq_ty.Coq_int,
         (Obj.magic Z.of_N (N.pow (Npos (Coq_xO Coq_xH)) (N.of_nat xlenbits)))))))),
         (RiscvPmpSignature.Coq_asn.Coq_sep
         ((RiscvPmpSignature.Coq_asn.Coq_chunk
         (RiscvPmpSignature.Coq_chunk_user ((Coq_inv_mmio bytes),
         Coq_env.Coq_nil))), (RiscvPmpSignature.Coq_asn.Coq_chunk
         (RiscvPmpSignature.Coq_chunk_user ((Coq_mmio_checked_write bytes),
         (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
         RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
         Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
         (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
         RiscvPmpBase.ty_xlenbits, (S (S (S (S O)))))))), (Coq_ty.Coq_bvec
         (mul bytes byte)), (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            EmptyString))))))))),
         (Coq_ty.Coq_bvec (mul bytes byte)), (S (S (S O))))))))))))))))
         (RiscvPmpSignature.Coq_asn.Coq_sep
         ((RiscvPmpSignature.Coq_asn.Coq_exist
         ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            EmptyString))),
         (Coq_ty.Coq_bvec (mul bytes byte)),
         (RiscvPmpSignature.Coq_asn.Coq_chunk
         (RiscvPmpSignature.Coq_chunk_user ((Coq_ptstomem bytes),
         (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
         RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
         Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
         (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
         RiscvPmpBase.ty_xlenbits, (S (S (S (S (S O))))))))),
         (Coq_ty.Coq_bvec (mul bytes byte)), (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            EmptyString))),
         (Coq_ty.Coq_bvec (mul bytes byte)), O))))))))),
         (RiscvPmpSignature.Coq_asn.Coq_sep
         ((RiscvPmpSignature.Coq_asn.Coq_formula
         (RiscvPmpSignature.Coq_formula_relop (Coq_ty.Coq_int,
         Coq_bop.Coq_le, (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int,
         (Obj.magic Z.of_N minAddr))), (RiscvPmpBase.Coq_term_unop
         ((Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))), Coq_ty.Coq_int,
         (Coq_uop.Coq_unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))), (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
         (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))), (S (S (S (S O))))))))))),
         (RiscvPmpSignature.Coq_asn.Coq_formula
         (RiscvPmpSignature.Coq_formula_relop (Coq_ty.Coq_int,
         Coq_bop.Coq_le, (RiscvPmpBase.Coq_term_binop (Coq_ty.Coq_int,
         Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_bop.Coq_plus,
         (RiscvPmpBase.Coq_term_unop ((Coq_ty.Coq_bvec (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S O))))))))))))))))))))))))))))))))), Coq_ty.Coq_int,
         (Coq_uop.Coq_unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))), (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
         (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))), (S (S (S (S O)))))))),
         (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int,
         (Obj.magic Z.of_nat bytes))))), (RiscvPmpBase.Coq_term_val
         (Coq_ty.Coq_int, (Obj.magic Z.of_N maxAddr))))))))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_chunk
      (RiscvPmpSignature.Coq_chunk_ptsreg (RiscvPmpBase.ty_privilege,
      RiscvPmpBase.Coq_cur_privilege, (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_privilege, (S O)))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop (RiscvPmpBase.ty_privilege,
      (Coq_bop.Coq_eq RiscvPmpBase.ty_privilege), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_privilege, (S O))), (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_privilege, (Obj.magic Machine)))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
      (Coq_pmp_entries, (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))))))),
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), O))))))),
      (RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_user (Coq_pmp_access, (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
      (Coq_ty.Coq_bvec xlenbits))), (Coq_ty.Coq_list
      RiscvPmpBase.ty_pmpentry))), RiscvPmpBase.ty_privilege)),
      (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
      (Coq_ty.Coq_bvec xlenbits))), (Coq_ty.Coq_list
      RiscvPmpBase.ty_pmpentry))), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
      (Coq_ty.Coq_bvec xlenbits))), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_xlenbits, (S (S (S (S O)))))))), (Coq_ty.Coq_bvec
      xlenbits), (RiscvPmpBase.Coq_term_unop (Coq_ty.Coq_int,
      (Coq_ty.Coq_bvec xlenbits), (Coq_uop.Coq_get_slice_int xlenbits),
      (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int,
      (Obj.magic Z.of_nat bytes))))))), (Coq_ty.Coq_list
      RiscvPmpBase.ty_pmpentry), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))))))),
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), O)))),
      RiscvPmpBase.ty_privilege, (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_privilege, (S O))))), RiscvPmpBase.ty_access_type,
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))),
      RiscvPmpBase.ty_access_type, (S (S O)))))))))))))))));
      RiscvPmpSignature.sep_contract_result =
      (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))))))))))))))))))))))))));
      RiscvPmpSignature.sep_contract_postcondition =
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop ((Coq_ty.Coq_union
      (Obj.magic (Coq_memory_op_result (S O)))), (Coq_bop.Coq_eq
      (Coq_ty.Coq_union (Obj.magic (Coq_memory_op_result (S O))))),
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_true, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)),
         EmptyString))))))))))))))))))))))))))))))))),
      (Coq_ty.Coq_union (Obj.magic (Coq_memory_op_result (S O)))), O)),
      (RiscvPmpBase.Coq_term_union ((Obj.magic (Coq_memory_op_result (S O))),
      (Obj.magic KMemValue), (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_byte, (Obj.magic (Npos Coq_xH))))))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.match_bool (Coq_ctx.Coq_snoc
         ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
         ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
         (Coq_ctx.Coq_nil, { Binding.name =
         (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
           Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), EmptyString)))))));
         Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), EmptyString)))))))))));
         Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
           EmptyString)))))))));
         Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) })),
         { Binding.name =
         (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), EmptyString)))))));
         Binding.coq_type = RiscvPmpBase.ty_access_type })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
           Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString)));
         Binding.coq_type = RiscvPmpBase.ty_privilege })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
           EmptyString)))))))))))))));
         Binding.coq_type = (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry) })),
         { Binding.name =
         (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
           Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
           Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
           Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
           Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
           Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
           EmptyString)))))))))))))))))))))))))))))))));
         Binding.coq_type = (RiscvPmpBase.ty_memory_op_result (S O)) }))
         (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), EmptyString))))))),
         Coq_ty.Coq_bool, (S (S (S (S (S (S O))))))))
         (RiscvPmpSignature.Coq_asn.Coq_formula
         (RiscvPmpSignature.Coq_formula_bool (RiscvPmpBase.Coq_term_val
         (Coq_ty.Coq_bool, (Obj.magic Coq_true)))))
         (RiscvPmpSignature.Coq_asn.Coq_chunk
         (RiscvPmpSignature.Coq_chunk_user ((Coq_ptstomem bytes),
         (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
         RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
         Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
         (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
         RiscvPmpBase.ty_xlenbits, (S (S (S (S (S O))))))))),
         (Coq_ty.Coq_bvec (mul bytes byte)), (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            EmptyString))))))))),
         (Coq_ty.Coq_bvec (mul bytes byte)), (S (S (S (S O)))))))))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_chunk
      (RiscvPmpSignature.Coq_chunk_ptsreg (RiscvPmpBase.ty_privilege,
      RiscvPmpBase.Coq_cur_privilege, (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_privilege, (S (S O))))))),
      (RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
      (Coq_pmp_entries, (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))))))),
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), (S O)))))))))))))) }

  (** val sep_contract_mem_read :
      nat -> RiscvPmpSpecification.coq_SepContractFun **)

  let sep_contract_mem_read bytes =
    { RiscvPmpSignature.sep_contract_logic_variables = (Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))));
      Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))));
      Binding.coq_type = RiscvPmpBase.ty_access_type })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), EmptyString)))))))))))))));
      Binding.coq_type = (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry) })),
      { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) }));
      RiscvPmpSignature.sep_contract_localstore = (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))));
      Binding.coq_type = RiscvPmpBase.ty_access_type })), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))));
      Binding.coq_type = RiscvPmpBase.ty_access_type },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))),
      RiscvPmpBase.ty_access_type, (S (S (S O))))))), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_xlenbits, (S (S O))))));
      RiscvPmpSignature.sep_contract_precondition =
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.match_bool (Coq_ctx.Coq_snoc
         ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
         ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
         (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
           Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), EmptyString)))))));
         Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), EmptyString)))))));
         Binding.coq_type = RiscvPmpBase.ty_access_type })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), EmptyString)))))))))));
         Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
           EmptyString)))))))))))))));
         Binding.coq_type = (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry) })),
         { Binding.name =
         (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
         Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) }))
         (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), EmptyString))))))),
         Coq_ty.Coq_bool, (S (S (S (S O))))))
         (RiscvPmpSignature.Coq_asn.Coq_chunk
         (RiscvPmpSignature.Coq_chunk_user ((Coq_ptstomem_readonly bytes),
         (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
         RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
         Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
         (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
         RiscvPmpBase.ty_xlenbits, (S (S O)))))), (Coq_ty.Coq_bvec
         (mul bytes byte)), (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            EmptyString))),
         (Coq_ty.Coq_bvec (mul bytes byte)), O)))))))
         (RiscvPmpSignature.Coq_asn.Coq_chunk
         (RiscvPmpSignature.Coq_chunk_user ((Coq_ptstomem bytes),
         (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
         RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
         Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
         (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
         RiscvPmpBase.ty_xlenbits, (S (S O)))))), (Coq_ty.Coq_bvec
         (mul bytes byte)), (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            EmptyString))),
         (Coq_ty.Coq_bvec (mul bytes byte)), O)))))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop (Coq_ty.Coq_int, Coq_bop.Coq_le,
      (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int,
      (Obj.magic Z.of_N minAddr))), (RiscvPmpBase.Coq_term_unop
      ((Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))), Coq_ty.Coq_int,
      (Coq_uop.Coq_unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))), (S (S O))))))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop (Coq_ty.Coq_int, Coq_bop.Coq_le,
      (RiscvPmpBase.Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int,
      Coq_ty.Coq_int, Coq_bop.Coq_plus, (RiscvPmpBase.Coq_term_unop
      ((Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))), Coq_ty.Coq_int,
      (Coq_uop.Coq_unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))), (S (S O)))))),
      (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int,
      (Obj.magic Z.of_nat bytes))))), (RiscvPmpBase.Coq_term_val
      (Coq_ty.Coq_int, (Obj.magic Z.of_N maxAddr)))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_chunk
      (RiscvPmpSignature.Coq_chunk_ptsreg (RiscvPmpBase.ty_privilege,
      RiscvPmpBase.Coq_cur_privilege, (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_privilege, (Obj.magic Machine)))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
      (Coq_pmp_entries, (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))))))),
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), (S O)))))))),
      (RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_user (Coq_pmp_access, (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
      (Coq_ty.Coq_bvec xlenbits))), (Coq_ty.Coq_list
      RiscvPmpBase.ty_pmpentry))), RiscvPmpBase.ty_privilege)),
      (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
      (Coq_ty.Coq_bvec xlenbits))), (Coq_ty.Coq_list
      RiscvPmpBase.ty_pmpentry))), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
      (Coq_ty.Coq_bvec xlenbits))), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_xlenbits, (S (S O)))))), (Coq_ty.Coq_bvec xlenbits),
      (RiscvPmpBase.Coq_term_unop (Coq_ty.Coq_int, (Coq_ty.Coq_bvec
      xlenbits), (Coq_uop.Coq_get_slice_int xlenbits),
      (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int,
      (Obj.magic Z.of_nat bytes))))))), (Coq_ty.Coq_list
      RiscvPmpBase.ty_pmpentry), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))))))),
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), (S O))))),
      RiscvPmpBase.ty_privilege, (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_privilege, (Obj.magic Machine))))),
      RiscvPmpBase.ty_access_type, (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))),
      RiscvPmpBase.ty_access_type, (S (S (S O))))))))))))))))))));
      RiscvPmpSignature.sep_contract_result =
      (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))))))))))))))))))))))))))));
      RiscvPmpSignature.sep_contract_postcondition =
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop ((Coq_ty.Coq_union
      (Obj.magic (Coq_memory_op_result bytes))), (Coq_bop.Coq_eq
      (Coq_ty.Coq_union (Obj.magic (Coq_memory_op_result bytes)))),
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_true, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))))))))))))))))))))))))))),
      (Coq_ty.Coq_union (Obj.magic (Coq_memory_op_result bytes))), O)),
      (RiscvPmpBase.Coq_term_union ((Obj.magic (Coq_memory_op_result bytes)),
      (Obj.magic KMemValue), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
      (RiscvPmpBase.typedefkit.Coq_ty.unionk_ty
        (Obj.magic (Coq_memory_op_result bytes)) (Obj.magic KMemValue)),
      (S O)))))))), (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.match_bool (Coq_ctx.Coq_snoc
         ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
         ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
         { Binding.name =
         (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
           Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), EmptyString)))))));
         Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), EmptyString)))))));
         Binding.coq_type = RiscvPmpBase.ty_access_type })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), EmptyString)))))))))));
         Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
           EmptyString)))))))))))))));
         Binding.coq_type = (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry) })),
         { Binding.name =
         (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
         Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) })),
         { Binding.name =
         (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
           Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
           Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
           Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
           Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), EmptyString)))))))))))))))))))))))))))))));
         Binding.coq_type = (RiscvPmpBase.ty_memory_op_result bytes) }))
         (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), EmptyString))))))),
         Coq_ty.Coq_bool, (S (S (S (S (S O)))))))
         (RiscvPmpSignature.Coq_asn.Coq_chunk
         (RiscvPmpSignature.Coq_chunk_user ((Coq_ptstomem_readonly bytes),
         (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
         RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
         Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
         (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
         RiscvPmpBase.ty_xlenbits, (S (S (S O))))))), (Coq_ty.Coq_bvec
         (mul bytes byte)), (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            EmptyString))),
         (Coq_ty.Coq_bvec (mul bytes byte)), (S O))))))))
         (RiscvPmpSignature.Coq_asn.Coq_chunk
         (RiscvPmpSignature.Coq_chunk_user ((Coq_ptstomem bytes),
         (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
         RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
         Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
         (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
         RiscvPmpBase.ty_xlenbits, (S (S (S O))))))), (Coq_ty.Coq_bvec
         (mul bytes byte)), (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            EmptyString))),
         (Coq_ty.Coq_bvec (mul bytes byte)), (S O))))))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_chunk
      (RiscvPmpSignature.Coq_chunk_ptsreg (RiscvPmpBase.ty_privilege,
      RiscvPmpBase.Coq_cur_privilege, (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_privilege, (Obj.magic Machine)))))),
      (RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
      (Coq_pmp_entries, (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))))))),
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), (S (S O))))))))))))))) }

  (** val sep_contract_mem_write_value :
      nat -> RiscvPmpSpecification.coq_SepContractFun **)

  let sep_contract_mem_write_value bytes =
    { RiscvPmpSignature.sep_contract_logic_variables = (Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))));
      Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString)))))))));
      Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), EmptyString)))))))))))))));
      Binding.coq_type = (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry) }));
      RiscvPmpSignature.sep_contract_localstore = (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits })), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_xlenbits, (S (S O)))))), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))))))));
      Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))))))))),
      (RiscvPmpBase.ty_bytes bytes), (S O)))));
      RiscvPmpSignature.sep_contract_precondition =
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.match_bool (Coq_ctx.Coq_snoc
         ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
         (Coq_ctx.Coq_nil, { Binding.name =
         (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
           Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), EmptyString)))))));
         Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), EmptyString)))))))))));
         Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
           EmptyString)))))))));
         Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) })),
         { Binding.name =
         (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
           EmptyString)))))))))))))));
         Binding.coq_type = (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry) }))
         (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), EmptyString))))))),
         Coq_ty.Coq_bool, (S (S (S O))))) (RiscvPmpSignature.Coq_asn.Coq_sep
         ((RiscvPmpSignature.Coq_asn.Coq_formula
         (RiscvPmpSignature.Coq_formula_user ((Coq_in_mmio bytes),
         (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
         RiscvPmpBase.ty_xlenbits, (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
         RiscvPmpBase.ty_xlenbits, (S (S O))))))))),
         (RiscvPmpSignature.Coq_asn.Coq_sep
         ((RiscvPmpSignature.Coq_asn.Coq_formula
         (RiscvPmpSignature.Coq_formula_relop (Coq_ty.Coq_int,
         Coq_bop.Coq_lt, (RiscvPmpBase.Coq_term_binop (Coq_ty.Coq_int,
         Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_bop.Coq_plus,
         (RiscvPmpBase.Coq_term_unop ((Coq_ty.Coq_bvec (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S O))))))))))))))))))))))))))))))))), Coq_ty.Coq_int,
         (Coq_uop.Coq_unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))), (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
         (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))), (S (S O)))))),
         (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int,
         (Obj.magic Z.of_nat bytes))))), (RiscvPmpBase.Coq_term_val
         (Coq_ty.Coq_int,
         (Obj.magic Z.of_N (N.pow (Npos (Coq_xO Coq_xH)) (N.of_nat xlenbits)))))))),
         (RiscvPmpSignature.Coq_asn.Coq_sep
         ((RiscvPmpSignature.Coq_asn.Coq_chunk
         (RiscvPmpSignature.Coq_chunk_user ((Coq_inv_mmio bytes),
         Coq_env.Coq_nil))), (RiscvPmpSignature.Coq_asn.Coq_chunk
         (RiscvPmpSignature.Coq_chunk_user ((Coq_mmio_checked_write bytes),
         (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
         RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
         Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
         (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
         RiscvPmpBase.ty_xlenbits, (S (S O)))))), (Coq_ty.Coq_bvec
         (mul bytes byte)), (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            EmptyString))))))))),
         (Coq_ty.Coq_bvec (mul bytes byte)), (S O))))))))))))))
         (RiscvPmpSignature.Coq_asn.Coq_sep
         ((RiscvPmpSignature.Coq_asn.Coq_exist
         ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            EmptyString))),
         (Coq_ty.Coq_bvec (mul bytes byte)),
         (RiscvPmpSignature.Coq_asn.Coq_chunk
         (RiscvPmpSignature.Coq_chunk_user ((Coq_ptstomem bytes),
         (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
         RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
         Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
         (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
         RiscvPmpBase.ty_xlenbits, (S (S (S O))))))), (Coq_ty.Coq_bvec
         (mul bytes byte)), (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            EmptyString))),
         (Coq_ty.Coq_bvec (mul bytes byte)), O))))))))),
         (RiscvPmpSignature.Coq_asn.Coq_sep
         ((RiscvPmpSignature.Coq_asn.Coq_formula
         (RiscvPmpSignature.Coq_formula_relop (Coq_ty.Coq_int,
         Coq_bop.Coq_le, (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int,
         (Obj.magic Z.of_N minAddr))), (RiscvPmpBase.Coq_term_unop
         ((Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))), Coq_ty.Coq_int,
         (Coq_uop.Coq_unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))), (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
         (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))), (S (S O))))))))),
         (RiscvPmpSignature.Coq_asn.Coq_formula
         (RiscvPmpSignature.Coq_formula_relop (Coq_ty.Coq_int,
         Coq_bop.Coq_le, (RiscvPmpBase.Coq_term_binop (Coq_ty.Coq_int,
         Coq_ty.Coq_int, Coq_ty.Coq_int, Coq_bop.Coq_plus,
         (RiscvPmpBase.Coq_term_unop ((Coq_ty.Coq_bvec (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S O))))))))))))))))))))))))))))))))), Coq_ty.Coq_int,
         (Coq_uop.Coq_unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))), (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
         (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))), (S (S O)))))),
         (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int,
         (Obj.magic Z.of_nat bytes))))), (RiscvPmpBase.Coq_term_val
         (Coq_ty.Coq_int, (Obj.magic Z.of_N maxAddr))))))))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_chunk
      (RiscvPmpSignature.Coq_chunk_ptsreg (RiscvPmpBase.ty_privilege,
      RiscvPmpBase.Coq_cur_privilege, (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_privilege, (Obj.magic Machine)))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
      (Coq_pmp_entries, (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))))))),
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), O))))))),
      (RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_user (Coq_pmp_access, (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
      (Coq_ty.Coq_bvec xlenbits))), (Coq_ty.Coq_list
      RiscvPmpBase.ty_pmpentry))), RiscvPmpBase.ty_privilege)),
      (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
      (Coq_ty.Coq_bvec xlenbits))), (Coq_ty.Coq_list
      RiscvPmpBase.ty_pmpentry))), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
      (Coq_ty.Coq_bvec xlenbits))), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_xlenbits, (S (S O)))))), (Coq_ty.Coq_bvec xlenbits),
      (RiscvPmpBase.Coq_term_unop (Coq_ty.Coq_int, (Coq_ty.Coq_bvec
      xlenbits), (Coq_uop.Coq_get_slice_int xlenbits),
      (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int,
      (Obj.magic Z.of_nat bytes))))))), (Coq_ty.Coq_list
      RiscvPmpBase.ty_pmpentry), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))))))),
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), O)))),
      RiscvPmpBase.ty_privilege, (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_privilege, (Obj.magic Machine))))),
      RiscvPmpBase.ty_access_type, (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_access_type, (Obj.magic Write))))))))))))));
      RiscvPmpSignature.sep_contract_result =
      (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))))))))))))))))))))))))));
      RiscvPmpSignature.sep_contract_postcondition =
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop ((Coq_ty.Coq_union
      (Obj.magic (Coq_memory_op_result (S O)))), (Coq_bop.Coq_eq
      (Coq_ty.Coq_union (Obj.magic (Coq_memory_op_result (S O))))),
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_true, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)),
         EmptyString))))))))))))))))))))))))))))))))),
      (Coq_ty.Coq_union (Obj.magic (Coq_memory_op_result (S O)))), O)),
      (RiscvPmpBase.Coq_term_union ((Obj.magic (Coq_memory_op_result (S O))),
      (Obj.magic KMemValue), (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_byte, (Obj.magic (Npos Coq_xH))))))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.match_bool (Coq_ctx.Coq_snoc
         ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
         ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
         (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
           Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), EmptyString)))))));
         Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), EmptyString)))))))))));
         Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
           EmptyString)))))))));
         Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) })),
         { Binding.name =
         (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
           EmptyString)))))))))))))));
         Binding.coq_type = (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry) })),
         { Binding.name =
         (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
           Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
           Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
           Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
           Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
           Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
           EmptyString)))))))))))))))))))))))))))))))));
         Binding.coq_type = (RiscvPmpBase.ty_memory_op_result (S O)) }))
         (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), EmptyString))))))),
         Coq_ty.Coq_bool, (S (S (S (S O))))))
         (RiscvPmpSignature.Coq_asn.Coq_formula
         (RiscvPmpSignature.Coq_formula_bool (RiscvPmpBase.Coq_term_val
         (Coq_ty.Coq_bool, (Obj.magic Coq_true)))))
         (RiscvPmpSignature.Coq_asn.Coq_chunk
         (RiscvPmpSignature.Coq_chunk_user ((Coq_ptstomem bytes),
         (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
         RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
         Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
         (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
         RiscvPmpBase.ty_xlenbits, (S (S (S O))))))), (Coq_ty.Coq_bvec
         (mul bytes byte)), (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            EmptyString))))))))),
         (Coq_ty.Coq_bvec (mul bytes byte)), (S (S O)))))))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_chunk
      (RiscvPmpSignature.Coq_chunk_ptsreg (RiscvPmpBase.ty_privilege,
      RiscvPmpBase.Coq_cur_privilege, (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_privilege, (Obj.magic Machine)))))),
      (RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
      (Coq_pmp_entries, (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))))))),
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry), (S O)))))))))))))) }

  (** val sep_contract_tick_pc : RiscvPmpSpecification.coq_SepContractFun **)

  let sep_contract_tick_pc =
    { RiscvPmpSignature.sep_contract_logic_variables = (Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false)), EmptyString)))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false)), EmptyString)))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits }));
      RiscvPmpSignature.sep_contract_localstore = Coq_env.Coq_nil;
      RiscvPmpSignature.sep_contract_precondition =
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_chunk
      (RiscvPmpSignature.Coq_chunk_ptsreg (RiscvPmpBase.ty_xlenbits,
      RiscvPmpBase.Coq_pc, (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), EmptyString))))),
      RiscvPmpBase.ty_xlenbits, (S O)))))),
      (RiscvPmpSignature.Coq_asn.Coq_chunk
      (RiscvPmpSignature.Coq_chunk_ptsreg (RiscvPmpBase.ty_xlenbits,
      RiscvPmpBase.Coq_nextpc, (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), EmptyString))))),
      RiscvPmpBase.ty_xlenbits, O)))))));
      RiscvPmpSignature.sep_contract_result =
      (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_true, Coq_true, Coq_false, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_true, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))))))))))))))))))))));
      RiscvPmpSignature.sep_contract_postcondition =
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_chunk
      (RiscvPmpSignature.Coq_chunk_ptsreg (RiscvPmpBase.ty_xlenbits,
      RiscvPmpBase.Coq_pc, (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), EmptyString))))),
      RiscvPmpBase.ty_xlenbits, (S O)))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_chunk
      (RiscvPmpSignature.Coq_chunk_ptsreg (RiscvPmpBase.ty_xlenbits,
      RiscvPmpBase.Coq_nextpc, (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), EmptyString))))),
      RiscvPmpBase.ty_xlenbits, (S O)))))),
      (RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop (Coq_ty.Coq_unit, (Coq_bop.Coq_eq
      Coq_ty.Coq_unit), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
         Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_true, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), EmptyString))))))))))))))))))))))))))))),
      Coq_ty.Coq_unit, O)), (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_unit,
      (Obj.magic Coq_tt)))))))))) }

  (** val sep_contract_within_phys_mem :
      RiscvPmpSpecification.coq_SepContractFun **)

  let sep_contract_within_phys_mem =
    { RiscvPmpSignature.sep_contract_logic_variables = (Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = Coq_ty.Coq_int }));
      RiscvPmpSignature.sep_contract_localstore = (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits })), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_xlenbits, (S O))))), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = Coq_ty.Coq_int }, (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), EmptyString))))))))))),
      Coq_ty.Coq_int, O)))); RiscvPmpSignature.sep_contract_precondition =
      (let paddr_int = RiscvPmpBase.Coq_term_unop ((Coq_ty.Coq_bvec (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S O))))))))))))))))))))))))))))))))),
         Coq_ty.Coq_int, (Coq_uop.Coq_unsigned (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))), (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
         (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))), (S O))))
       in
       RiscvPmpSignature.Coq_asn.Coq_sep
       ((RiscvPmpSignature.Coq_asn.Coq_formula
       (RiscvPmpSignature.Coq_formula_relop (Coq_ty.Coq_int, Coq_bop.Coq_le,
       (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int,
       (Obj.magic Z.of_N minAddr))), paddr_int))),
       (RiscvPmpSignature.Coq_asn.Coq_formula
       (RiscvPmpSignature.Coq_formula_relop (Coq_ty.Coq_int, Coq_bop.Coq_le,
       (RiscvPmpBase.Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int,
       Coq_ty.Coq_int, Coq_bop.Coq_plus, paddr_int,
       (RiscvPmpBase.Coq_term_var
       ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
          Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
          (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
          Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
          Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
          (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
          Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
          (Coq_false, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
          Coq_true, Coq_false)), EmptyString))))))))))),
       Coq_ty.Coq_int, O)))), (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int,
       (Obj.magic Z.of_N maxAddr))))))));
      RiscvPmpSignature.sep_contract_result =
      (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))))))))))))))))))))))))))))))))))))))))));
      RiscvPmpSignature.sep_contract_postcondition =
      (RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop (Coq_ty.Coq_bool, (Coq_bop.Coq_eq
      Coq_ty.Coq_bool), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_true, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_false)),
         EmptyString))))))))))))))))))))))))))))))))))))))))))))),
      Coq_ty.Coq_bool, O)), (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_bool,
      (Obj.magic Coq_true)))))) }

  (** val sep_contract_execute_EBREAK :
      RiscvPmpSpecification.coq_SepContractFun **)

  let sep_contract_execute_EBREAK =
    RiscvPmpExecutor.Symbolic.Statistics.extend_postcond_with_debug
      Coq_ctx.Coq_nil RiscvPmpBase.ty_retired
      RiscvPmpSpecification.sep_contract_execute_EBREAK

  (** val coq_CEnv : RiscvPmpSpecification.coq_SepContractEnv **)

  let coq_CEnv _ _ = function
  | RiscvPmpProgram.Coq_rX -> Some sep_contract_rX
  | RiscvPmpProgram.Coq_wX -> Some sep_contract_wX
  | RiscvPmpProgram.Coq_tick_pc -> Some sep_contract_tick_pc
  | RiscvPmpProgram.Coq_within_phys_mem -> Some sep_contract_within_phys_mem
  | RiscvPmpProgram.Coq_mem_read bytes -> Some (sep_contract_mem_read bytes)
  | RiscvPmpProgram.Coq_checked_mem_read bytes ->
    Some (sep_contract_checked_mem_read bytes)
  | RiscvPmpProgram.Coq_checked_mem_write bytes ->
    Some (sep_contract_checked_mem_write bytes)
  | RiscvPmpProgram.Coq_pmp_mem_read bytes ->
    Some (sep_contract_pmp_mem_read bytes)
  | RiscvPmpProgram.Coq_pmp_mem_write bytes ->
    Some (sep_contract_pmp_mem_write bytes)
  | RiscvPmpProgram.Coq_pmpCheck bytes -> Some (sep_contract_pmpCheck bytes)
  | RiscvPmpProgram.Coq_pmpMatchAddr ->
    Some RiscvPmpSpecification.sep_contract_pmpMatchAddr
  | RiscvPmpProgram.Coq_mem_write_value bytes ->
    Some (sep_contract_mem_write_value bytes)
  | RiscvPmpProgram.Coq_fetch -> Some sep_contract_fetch_instr
  | RiscvPmpProgram.Coq_execute_EBREAK -> Some sep_contract_execute_EBREAK
  | _ -> None

  (** val sep_contract_read_ram :
      nat -> RiscvPmpSpecification.coq_SepContractFunX **)

  let sep_contract_read_ram bytes =
    { RiscvPmpSignature.sep_contract_logic_variables = (Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))));
      Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) }));
      RiscvPmpSignature.sep_contract_localstore = (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_xlenbits, (S O)))));
      RiscvPmpSignature.sep_contract_precondition =
      (RiscvPmpSignature.Coq_asn.match_bool (Coq_ctx.Coq_snoc
        ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
        { Binding.name =
        (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
          Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
          (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
          Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
          Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
          EmptyString)))))));
        Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
        (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
          Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
          Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
          Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
          Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
          Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
          Coq_true, Coq_true, Coq_false)), EmptyString)))))))))));
        Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
        (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
          Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
        Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) }))
        (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
           Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), EmptyString))))))),
        Coq_ty.Coq_bool, (S (S O)))) (RiscvPmpSignature.Coq_asn.Coq_chunk
        (RiscvPmpSignature.Coq_chunk_user ((Coq_ptstomem_readonly bytes),
        (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
        RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
        Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits, (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
        RiscvPmpBase.ty_xlenbits, (S O))))), (Coq_ty.Coq_bvec
        (mul bytes byte)), (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
        (Coq_ty.Coq_bvec (mul bytes byte)), O)))))))
        (RiscvPmpSignature.Coq_asn.Coq_chunk
        (RiscvPmpSignature.Coq_chunk_user ((Coq_ptstomem bytes),
        (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
        RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
        Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits, (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
        RiscvPmpBase.ty_xlenbits, (S O))))), (Coq_ty.Coq_bvec
        (mul bytes byte)), (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
        (Coq_ty.Coq_bvec (mul bytes byte)), O))))))));
      RiscvPmpSignature.sep_contract_result =
      (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))))))))))))))))))))))))))));
      RiscvPmpSignature.sep_contract_postcondition =
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.match_bool (Coq_ctx.Coq_snoc
         ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
         (Coq_ctx.Coq_nil, { Binding.name =
         (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
           Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), EmptyString)))))));
         Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), EmptyString)))))))))));
         Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
         (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
         Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) })),
         { Binding.name =
         (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
           Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_false, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
           Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
           Coq_true, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_true, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
           Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
           Coq_false)), EmptyString)))))))))))))))))))))))))))))));
         Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) }))
         (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
            Coq_false)), EmptyString))))))),
         Coq_ty.Coq_bool, (S (S (S O)))))
         (RiscvPmpSignature.Coq_asn.Coq_chunk
         (RiscvPmpSignature.Coq_chunk_user ((Coq_ptstomem_readonly bytes),
         (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
         RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
         Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
         (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
         RiscvPmpBase.ty_xlenbits, (S (S O)))))), (Coq_ty.Coq_bvec
         (mul bytes byte)), (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            EmptyString))),
         (Coq_ty.Coq_bvec (mul bytes byte)), (S O))))))))
         (RiscvPmpSignature.Coq_asn.Coq_chunk
         (RiscvPmpSignature.Coq_chunk_user ((Coq_ptstomem bytes),
         (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
         RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
         Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
         (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
            Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
            Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
            Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
            ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
            Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
         RiscvPmpBase.ty_xlenbits, (S (S O)))))), (Coq_ty.Coq_bvec
         (mul bytes byte)), (RiscvPmpBase.Coq_term_var
         ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true,
            Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
            EmptyString))),
         (Coq_ty.Coq_bvec (mul bytes byte)), (S O))))))))),
      (RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop ((Coq_ty.Coq_bvec
      (let rec mul0 n m =
         match n with
         | O -> O
         | S p ->
           let rec add n0 m0 =
             match n0 with
             | O -> m0
             | S p0 -> S (add p0 m0)
           in add m (mul0 p m)
       in mul0 bytes (S (S (S (S (S (S (S (S O)))))))))),
      (Coq_bop.Coq_eq (Coq_ty.Coq_bvec
      (let rec mul0 n m =
         match n with
         | O -> O
         | S p ->
           let rec add n0 m0 =
             match n0 with
             | O -> m0
             | S p0 -> S (add p0 m0)
           in add m (mul0 p m)
       in mul0 bytes (S (S (S (S (S (S (S (S O))))))))))),
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
         Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))))))))))))))))))))))))))),
      (Coq_ty.Coq_bvec
      (let rec mul0 n m =
         match n with
         | O -> O
         | S p ->
           let rec add n0 m0 =
             match n0 with
             | O -> m0
             | S p0 -> S (add p0 m0)
           in add m (mul0 p m)
       in mul0 bytes (S (S (S (S (S (S (S (S O)))))))))),
      O)), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
      (Coq_ty.Coq_bvec
      (let rec mul0 n m =
         match n with
         | O -> O
         | S p ->
           let rec add n0 m0 =
             match n0 with
             | O -> m0
             | S p0 -> S (add p0 m0)
           in add m (mul0 p m)
       in mul0 bytes (S (S (S (S (S (S (S (S O)))))))))),
      (S O)))))))) }

  (** val sep_contract_write_ram :
      nat -> RiscvPmpSpecification.coq_SepContractFunX **)

  let sep_contract_write_ram bytes =
    { RiscvPmpSignature.sep_contract_logic_variables = (Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_word })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString)))))))));
      Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) }));
      RiscvPmpSignature.sep_contract_localstore = (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits })), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_xlenbits, (S O))))), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString)))))))));
      Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))))))))),
      (RiscvPmpBase.ty_bytes bytes), O))));
      RiscvPmpSignature.sep_contract_precondition =
      (RiscvPmpSignature.Coq_asn.Coq_exist
      ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
      (Coq_ty.Coq_bvec (mul bytes byte)),
      (RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
      ((Coq_ptstomem bytes), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_xlenbits, (S (S O)))))), (Coq_ty.Coq_bvec
      (mul bytes byte)), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
      (Coq_ty.Coq_bvec (mul bytes byte)), O)))))))));
      RiscvPmpSignature.sep_contract_result =
      (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
        Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_false)),
        EmptyString)))))))))))))))))))))))))))))))));
      RiscvPmpSignature.sep_contract_postcondition =
      (RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
      ((Coq_ptstomem bytes), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_xlenbits, (S (S O)))))), (Coq_ty.Coq_bvec
      (mul bytes byte)), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))))))))),
      (Coq_ty.Coq_bvec (mul bytes byte)), (S O)))))))) }

  (** val sep_contract_within_mmio :
      nat -> RiscvPmpSpecification.coq_SepContractFunX **)

  let sep_contract_within_mmio bytes =
    { RiscvPmpSignature.sep_contract_logic_variables = (Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))));
      Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits }));
      RiscvPmpSignature.sep_contract_localstore = (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_xlenbits, O))));
      RiscvPmpSignature.sep_contract_precondition =
      (RiscvPmpSignature.Coq_asn.match_bool (Coq_ctx.Coq_snoc
        ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
        (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
          Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
          (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
          Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
          Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
          EmptyString)))))));
        Binding.coq_type = Coq_ty.Coq_bool })), { Binding.name =
        (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
          Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
          Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
          Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
          Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
          Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
          Coq_true, Coq_true, Coq_false)), EmptyString)))))))))));
        Binding.coq_type = RiscvPmpBase.ty_xlenbits }))
        (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
           Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
           Coq_false)), EmptyString))))))),
        Coq_ty.Coq_bool, (S O))) (RiscvPmpSignature.Coq_asn.Coq_sep
        ((RiscvPmpSignature.Coq_asn.Coq_formula
        (RiscvPmpSignature.Coq_formula_user ((Coq_in_mmio bytes),
        (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
        RiscvPmpBase.ty_xlenbits, (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
        RiscvPmpBase.ty_xlenbits, O))))))),
        (RiscvPmpSignature.Coq_asn.Coq_formula
        (RiscvPmpSignature.Coq_formula_relop (Coq_ty.Coq_int, Coq_bop.Coq_lt,
        (RiscvPmpBase.Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int,
        Coq_ty.Coq_int, Coq_bop.Coq_plus, (RiscvPmpBase.Coq_term_unop
        ((Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))), Coq_ty.Coq_int,
        (Coq_uop.Coq_unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))), (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
        (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))), O)))), (RiscvPmpBase.Coq_term_val
        (Coq_ty.Coq_int, (Obj.magic Z.of_nat bytes))))),
        (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int,
        (Obj.magic Z.of_N (N.pow (Npos (Coq_xO Coq_xH)) (N.of_nat xlenbits))))))))))
        (RiscvPmpSignature.Coq_asn.Coq_sep
        ((RiscvPmpSignature.Coq_asn.Coq_formula
        (RiscvPmpSignature.Coq_formula_relop (Coq_ty.Coq_int, Coq_bop.Coq_le,
        (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int,
        (Obj.magic Z.of_N minAddr))), (RiscvPmpBase.Coq_term_unop
        ((Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))), Coq_ty.Coq_int,
        (Coq_uop.Coq_unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))), (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
        (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))), O))))))),
        (RiscvPmpSignature.Coq_asn.Coq_formula
        (RiscvPmpSignature.Coq_formula_relop (Coq_ty.Coq_int, Coq_bop.Coq_le,
        (RiscvPmpBase.Coq_term_binop (Coq_ty.Coq_int, Coq_ty.Coq_int,
        Coq_ty.Coq_int, Coq_bop.Coq_plus, (RiscvPmpBase.Coq_term_unop
        ((Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))), Coq_ty.Coq_int,
        (Coq_uop.Coq_unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))), (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
           Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
           Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
           Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
           Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
           Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
           ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
           Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
        (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))), O)))), (RiscvPmpBase.Coq_term_val
        (Coq_ty.Coq_int, (Obj.magic Z.of_nat bytes))))),
        (RiscvPmpBase.Coq_term_val (Coq_ty.Coq_int,
        (Obj.magic Z.of_N maxAddr)))))))));
      RiscvPmpSignature.sep_contract_result =
      (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
        Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))))))))))))))))))))))))));
      RiscvPmpSignature.sep_contract_postcondition =
      (RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop (Coq_ty.Coq_bool, (Coq_bop.Coq_eq
      Coq_ty.Coq_bool), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_false)),
         EmptyString))))))))))))))))))))))))))))))))),
      Coq_ty.Coq_bool, O)), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_true,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))),
      Coq_ty.Coq_bool, (S (S O))))))) }

  (** val sep_contract_mmio_write :
      nat -> RiscvPmpSpecification.coq_SepContractFunX **)

  let sep_contract_mmio_write bytes =
    { RiscvPmpSignature.sep_contract_logic_variables = (Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString)))))))));
      Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) }));
      RiscvPmpSignature.sep_contract_localstore = (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits })), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_xlenbits, (S O))))), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString)))))))));
      Binding.coq_type = (RiscvPmpBase.ty_bytes bytes) },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))))))))),
      (RiscvPmpBase.ty_bytes bytes), O))));
      RiscvPmpSignature.sep_contract_precondition =
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_user ((Coq_in_mmio bytes),
      (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
      RiscvPmpBase.ty_xlenbits, (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_xlenbits, (S O)))))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
      ((Coq_inv_mmio bytes), Coq_env.Coq_nil))),
      (RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
      ((Coq_mmio_checked_write bytes), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_xlenbits, (S O))))), (Coq_ty.Coq_bvec
      (mul bytes byte)), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))))))))),
      (Coq_ty.Coq_bvec (mul bytes byte)), O)))))))))));
      RiscvPmpSignature.sep_contract_result =
      (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
        Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_true,
        Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))))))))))))))))))))))))))))))));
      RiscvPmpSignature.sep_contract_postcondition =
      (RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_bool (RiscvPmpBase.Coq_term_val
      (Coq_ty.Coq_bool, (Obj.magic Coq_true))))) }

  (** val sep_contract_decode : RiscvPmpSpecification.coq_SepContractFunX **)

  let sep_contract_decode =
    { RiscvPmpSignature.sep_contract_logic_variables = (Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), EmptyString)))))))));
      Binding.coq_type = RiscvPmpBase.ty_word })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_ast }));
      RiscvPmpSignature.sep_contract_localstore = (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_true, Coq_false)), EmptyString)))));
      Binding.coq_type = RiscvPmpBase.ty_word }, (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))))))))),
      RiscvPmpBase.ty_word, (S O)))));
      RiscvPmpSignature.sep_contract_precondition =
      (RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
      (Coq_encodes_instr, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, RiscvPmpBase.ty_word)), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, RiscvPmpBase.ty_word,
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))))))))),
      RiscvPmpBase.ty_word, (S O))))), RiscvPmpBase.ty_ast,
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_ast, O))))))); RiscvPmpSignature.sep_contract_result =
      (Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
        EmptyString)))))))))))))))))))))))))));
      RiscvPmpSignature.sep_contract_postcondition =
      (RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop ((Coq_ty.Coq_union
      (Obj.magic Coq_ast)), (Coq_bop.Coq_eq (Coq_ty.Coq_union
      (Obj.magic Coq_ast))), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_true, Coq_true, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_true, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
         Coq_true, Coq_true, Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)),
         EmptyString))))))))))))))))))))))))))),
      (Coq_ty.Coq_union (Obj.magic Coq_ast)), O)), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         (String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_true, Coq_false)), EmptyString))))))))))),
      (Coq_ty.Coq_union (Obj.magic Coq_ast)), (S O)))))) }

  (** val coq_CEnvEx : RiscvPmpSpecification.coq_SepContractEnvEx **)

  let coq_CEnvEx _ _ = function
  | RiscvPmpProgram.Coq_read_ram bytes -> sep_contract_read_ram bytes
  | RiscvPmpProgram.Coq_write_ram bytes -> sep_contract_write_ram bytes
  | RiscvPmpProgram.Coq_mmio_read bytes ->
    RiscvPmpSpecification.sep_contract_mmio_read bytes
  | RiscvPmpProgram.Coq_mmio_write bytes -> sep_contract_mmio_write bytes
  | RiscvPmpProgram.Coq_within_mmio bytes -> sep_contract_within_mmio bytes
  | RiscvPmpProgram.Coq_decode -> sep_contract_decode
  | RiscvPmpProgram.Coq_externalWorldUpdates ->
    RiscvPmpSpecification.sep_contract_externalWorldUpdates

  (** val lemma_open_gprs : RiscvPmpSpecification.coq_SepLemma **)

  let lemma_open_gprs =
    { RiscvPmpSignature.lemma_logic_variables = Coq_ctx.Coq_nil;
      RiscvPmpSignature.lemma_patterns = Coq_env.Coq_nil;
      RiscvPmpSignature.lemma_precondition =
      (RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_bool (RiscvPmpBase.Coq_term_val
      (Coq_ty.Coq_bool, (Obj.magic Coq_true)))));
      RiscvPmpSignature.lemma_postcondition =
      (RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_bool (RiscvPmpBase.Coq_term_val
      (Coq_ty.Coq_bool, (Obj.magic Coq_true))))) }

  (** val lemma_close_gprs : RiscvPmpSpecification.coq_SepLemma **)

  let lemma_close_gprs =
    { RiscvPmpSignature.lemma_logic_variables = Coq_ctx.Coq_nil;
      RiscvPmpSignature.lemma_patterns = Coq_env.Coq_nil;
      RiscvPmpSignature.lemma_precondition =
      (RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_bool (RiscvPmpBase.Coq_term_val
      (Coq_ty.Coq_bool, (Obj.magic Coq_true)))));
      RiscvPmpSignature.lemma_postcondition =
      (RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_bool (RiscvPmpBase.Coq_term_val
      (Coq_ty.Coq_bool, (Obj.magic Coq_true))))) }

  (** val lemma_open_ptsto_instr : RiscvPmpSpecification.coq_SepLemma **)

  let lemma_open_ptsto_instr =
    { RiscvPmpSignature.lemma_logic_variables = (Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_word })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_ast }));
      RiscvPmpSignature.lemma_patterns = (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
      Coq_env.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_xlenbits, (S O)))));
      RiscvPmpSignature.lemma_precondition =
      (RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
      (Coq_ptstoinstr, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
      Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits, (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_xlenbits, (S O))))), RiscvPmpBase.ty_ast,
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_ast, O))))))); RiscvPmpSignature.lemma_postcondition =
      (RiscvPmpSignature.Coq_asn.Coq_exist
      ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
      (Coq_ty.Coq_bvec (mul bytes_per_word byte)),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
      ((Coq_ptstomem bytes_per_word), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_xlenbits, (S (S O)))))), (Coq_ty.Coq_bvec
      (mul bytes_per_word byte)), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
      (Coq_ty.Coq_bvec (mul bytes_per_word byte)), O))))))),
      (RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
      (Coq_encodes_instr, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, RiscvPmpBase.ty_word)), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, RiscvPmpBase.ty_word,
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_word, O)))), RiscvPmpBase.ty_ast,
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_ast, (S O)))))))))))) }

  (** val lemma_close_ptsto_instr : RiscvPmpSpecification.coq_SepLemma **)

  let lemma_close_ptsto_instr =
    { RiscvPmpSignature.lemma_logic_variables = (Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_word })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_word })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_ast }));
      RiscvPmpSignature.lemma_patterns = (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits })), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_xlenbits, (S (S O)))))), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_xlenbits, (S O)))));
      RiscvPmpSignature.lemma_precondition =
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
      ((Coq_ptstomem bytes_per_word), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits,
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_xlenbits, (S (S O)))))), (Coq_ty.Coq_bvec
      (mul bytes_per_word byte)), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
      (Coq_ty.Coq_bvec (mul bytes_per_word byte)), (S O)))))))),
      (RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
      (Coq_encodes_instr, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, RiscvPmpBase.ty_word)), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, RiscvPmpBase.ty_word,
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_word, (S O))))), RiscvPmpBase.ty_ast,
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_ast, O)))))))));
      RiscvPmpSignature.lemma_postcondition =
      (RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
      (Coq_ptstoinstr, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
      Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits, (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_xlenbits, (S (S O)))))), RiscvPmpBase.ty_ast,
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_ast, O))))))) }

  (** val lemma_extract_pmp_ptsto :
      nat -> RiscvPmpSpecification.coq_SepLemma **)

  let lemma_extract_pmp_ptsto _ =
    { RiscvPmpSignature.lemma_logic_variables = (Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits }));
      RiscvPmpSignature.lemma_patterns = (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
      Coq_env.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_xlenbits, O)))); RiscvPmpSignature.lemma_precondition =
      (RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_bool (RiscvPmpBase.Coq_term_val
      (Coq_ty.Coq_bool, (Obj.magic Coq_true)))));
      RiscvPmpSignature.lemma_postcondition =
      (RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_bool (RiscvPmpBase.Coq_term_val
      (Coq_ty.Coq_bool, (Obj.magic Coq_true))))) }

  (** val lemma_return_pmp_ptsto :
      nat -> RiscvPmpSpecification.coq_SepLemma **)

  let lemma_return_pmp_ptsto _ =
    { RiscvPmpSignature.lemma_logic_variables = (Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits }));
      RiscvPmpSignature.lemma_patterns = (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
      Coq_env.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_xlenbits, O)))); RiscvPmpSignature.lemma_precondition =
      (RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_bool (RiscvPmpBase.Coq_term_val
      (Coq_ty.Coq_bool, (Obj.magic Coq_true)))));
      RiscvPmpSignature.lemma_postcondition =
      (RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_bool (RiscvPmpBase.Coq_term_val
      (Coq_ty.Coq_bool, (Obj.magic Coq_true))))) }

  (** val map_wordwidth : coq_WordWidth -> nat **)

  let map_wordwidth = function
  | BYTE -> S O
  | HALF -> S (S O)
  | WORD -> S (S (S (S O)))

  (** val lemma_close_mmio_write :
      Coq_bv.bv -> coq_WordWidth -> RiscvPmpSpecification.coq_SepLemma **)

  let lemma_close_mmio_write immm widthh =
    { RiscvPmpSignature.lemma_logic_variables = (Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits }));
      RiscvPmpSignature.lemma_patterns = (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits })), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_true,
        Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
        Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
        ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_true,
        Coq_false)), EmptyString)))))))))));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      RiscvPmpBase.ty_xlenbits, (S O))))), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
        Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits },
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_xlenbits, O)))); RiscvPmpSignature.lemma_precondition =
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop (RiscvPmpBase.ty_xlenbits,
      (Coq_bop.Coq_eq RiscvPmpBase.ty_xlenbits), (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_xlenbits,
      (Obj.magic RiscvPmpIrisInstancePredicates.write_addr))),
      (RiscvPmpBase.Coq_term_binop ((Coq_ty.Coq_bvec xlenbits),
      (Coq_ty.Coq_bvec xlenbits), (Coq_ty.Coq_bvec xlenbits),
      (Coq_bop.Coq_bvadd xlenbits), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      (Coq_ty.Coq_bvec xlenbits), (S O))), (RiscvPmpBase.Coq_term_unop
      ((Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))),
      (Coq_ty.Coq_bvec xlenbits), (Coq_uop.Coq_sext ((S (S (S (S (S (S (S (S
      (S (S (S (S O)))))))))))), xlenbits)), (RiscvPmpBase.Coq_term_val
      ((Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))),
      (Obj.magic immm)))))))))), (RiscvPmpSignature.Coq_asn.Coq_formula
      (RiscvPmpSignature.Coq_formula_relop (RiscvPmpBase.ty_xlenbits,
      (Coq_bop.Coq_eq RiscvPmpBase.ty_xlenbits), (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
         Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
      RiscvPmpBase.ty_xlenbits, O)), (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_xlenbits,
      (Obj.magic Coq_bv.of_nat xlenbits (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))))))))));
      RiscvPmpSignature.lemma_postcondition =
      (RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
      ((Coq_mmio_checked_write (map_wordwidth widthh)), (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, RiscvPmpBase.ty_xlenbits)),
      (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
      RiscvPmpBase.ty_xlenbits, (RiscvPmpBase.Coq_term_binop
      ((Coq_ty.Coq_bvec xlenbits), (Coq_ty.Coq_bvec xlenbits),
      (Coq_ty.Coq_bvec xlenbits), (Coq_bop.Coq_bvadd xlenbits),
      (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
         Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
         Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
         Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
         Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
         ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
         Coq_true, Coq_true, Coq_false)), EmptyString))))))))))),
      (Coq_ty.Coq_bvec xlenbits), (S O))), (RiscvPmpBase.Coq_term_unop
      ((Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))),
      (Coq_ty.Coq_bvec xlenbits), (Coq_uop.Coq_sext ((S (S (S (S (S (S (S (S
      (S (S (S (S O)))))))))))), xlenbits)), (RiscvPmpBase.Coq_term_val
      ((Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))),
      (Obj.magic immm))))))))), (Coq_ty.Coq_bvec
      (mul (map_wordwidth widthh) byte)),
      (RiscvPmpBase.term_truncate (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
        (Coq_ctx.Coq_nil, { Binding.name =
        (Obj.magic (String ((Ascii (Coq_false, Coq_false, Coq_false,
          Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false,
          Coq_true, Coq_true, Coq_false)), (String ((Ascii (Coq_false,
          Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
          Coq_false)), (String ((Ascii (Coq_false, Coq_false, Coq_true,
          Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
          Coq_true, Coq_true, Coq_false)), EmptyString)))))))))));
        Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
        (Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
          Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString)));
        Binding.coq_type = RiscvPmpBase.ty_xlenbits })) (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S O))))))))))))))))))))))))))))))))
        (mul (map_wordwidth widthh) byte) (RiscvPmpBase.Coq_term_var
        ((Obj.magic (String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false,
           Coq_true, Coq_true, Coq_true, Coq_false)), EmptyString))),
        (Coq_ty.Coq_bvec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))), O)))))))) }

  (** val coq_LEnv : RiscvPmpSpecification.coq_LemmaEnv **)

  let coq_LEnv _ = function
  | RiscvPmpProgram.Coq_open_gprs -> lemma_open_gprs
  | RiscvPmpProgram.Coq_close_gprs -> lemma_close_gprs
  | RiscvPmpProgram.Coq_open_pmp_entries ->
    RiscvPmpSpecification.lemma_open_pmp_entries
  | RiscvPmpProgram.Coq_close_pmp_entries ->
    RiscvPmpSpecification.lemma_close_pmp_entries
  | RiscvPmpProgram.Coq_extract_pmp_ptsto bytes ->
    lemma_extract_pmp_ptsto bytes
  | RiscvPmpProgram.Coq_return_pmp_ptsto bytes -> lemma_return_pmp_ptsto bytes
  | RiscvPmpProgram.Coq_open_ptsto_instr -> lemma_open_ptsto_instr
  | RiscvPmpProgram.Coq_close_ptsto_instr -> lemma_close_ptsto_instr
  | RiscvPmpProgram.Coq_close_mmio_write (immm, widthh) ->
    lemma_close_mmio_write immm widthh
 end

module RiscvPmpBlockVerifExecutor =
 MakeExecutor(RiscvPmpBase)(RiscvPmpSignature)(RiscvPmpProgram)(RiscvPmpBlockVerifFailLogic)(RiscvPmpBlockVerifSpec)
