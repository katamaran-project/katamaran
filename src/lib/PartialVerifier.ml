open Ascii
open Base1
open BinOps
open Context
open Datatypes
open Environment
open Machine
open Sig
open Spec
open String
open TypeDecl
open Variables

(** val exec_instruction_prologue :
    coq_AST -> RiscvPmpSignature.Coq_asn.coq_Assertion **)

let exec_instruction_prologue i =
  RiscvPmpSignature.Coq_asn.Coq_sep ((RiscvPmpSignature.Coq_asn.Coq_chunk
    (RiscvPmpSignature.Coq_chunk_ptsreg (RiscvPmpBase.ty_xlenbits,
    RiscvPmpBase.Coq_pc, (RiscvPmpBase.Coq_term_var
    ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
       Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))),
    RiscvPmpBase.ty_xlenbits, O))))), (RiscvPmpSignature.Coq_asn.Coq_sep
    ((RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
    (Coq_ptstoinstr, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
    RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
    Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits, (RiscvPmpBase.Coq_term_var
    ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
       Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))),
    RiscvPmpBase.ty_xlenbits, O)))), RiscvPmpBase.ty_ast,
    (RiscvPmpBase.Coq_term_val (RiscvPmpBase.ty_ast, (Obj.magic i)))))))),
    (RiscvPmpSignature.Coq_asn.Coq_exist
    ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
       Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
       (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
       Coq_true, Coq_false)), EmptyString))))),
    RiscvPmpBase.ty_xlenbits, (RiscvPmpSignature.Coq_asn.Coq_chunk
    (RiscvPmpSignature.Coq_chunk_ptsreg (RiscvPmpBase.ty_xlenbits,
    RiscvPmpBase.Coq_nextpc, (RiscvPmpBase.Coq_term_var
    ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
       Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
       (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
       Coq_true, Coq_false)), EmptyString))))),
    RiscvPmpBase.ty_xlenbits, O))))))))))

(** val exec_instruction_epilogue :
    coq_AST -> RiscvPmpSignature.Coq_asn.coq_Assertion **)

let exec_instruction_epilogue i =
  RiscvPmpSignature.Coq_asn.Coq_sep ((RiscvPmpSignature.Coq_asn.Coq_chunk
    (RiscvPmpSignature.Coq_chunk_ptsreg (RiscvPmpBase.ty_xlenbits,
    RiscvPmpBase.Coq_pc, (RiscvPmpBase.Coq_term_var
    ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
       Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
       (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
       Coq_true, Coq_false)), EmptyString))))),
    RiscvPmpBase.ty_xlenbits, O))))), (RiscvPmpSignature.Coq_asn.Coq_sep
    ((RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
    (Coq_ptstoinstr, (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
    RiscvPmpBase.ty_xlenbits)), (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
    Coq_env.Coq_nil, RiscvPmpBase.ty_xlenbits, (RiscvPmpBase.Coq_term_var
    ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
       Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString))),
    RiscvPmpBase.ty_xlenbits, (S O))))), RiscvPmpBase.ty_ast,
    (RiscvPmpBase.Coq_term_val (RiscvPmpBase.ty_ast, (Obj.magic i)))))))),
    (RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_ptsreg
    (RiscvPmpBase.ty_xlenbits, RiscvPmpBase.Coq_nextpc,
    (RiscvPmpBase.Coq_term_var
    ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
       Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
       (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
       Coq_true, Coq_false)), EmptyString))))),
    RiscvPmpBase.ty_xlenbits, O))))))))

(** val sexec_instruction :
    coq_AST -> (RiscvPmpBase.coq_Term, RiscvPmpBase.coq_Term
    RiscvPmpSignature.coq_SHeapSpec) RiscvPmpSignature.coq_Impl
    RiscvPmpSignature.coq_Valid **)

let sexec_instruction i =
  let inline_fuel = S (S (S (S (S (S (S (S (S (S O))))))))) in
  (fun w a ->
  RiscvPmpSignature.SHeapSpec.bind w
    (RiscvPmpSignature.SHeapSpec.produce (Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil,
      { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits }))
      (exec_instruction_prologue i) w (Coq_env.Coq_snoc (Coq_ctx.Coq_nil,
      Coq_env.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString)));
      Binding.coq_type = RiscvPmpBase.ty_xlenbits }, a)))
    (fun w1 _UU03b8_1 _ ->
    RiscvPmpSignature.SHeapSpec.bind w1
      (RiscvPmpBlockVerifExecutor.SStoreSpec.evalStoreSpec Coq_ctx.Coq_nil
        Coq_ctx.Coq_nil w1
        (RiscvPmpBlockVerifExecutor.sexec
          RiscvPmpBlockVerifExecutor.default_config inline_fuel
          Coq_ctx.Coq_nil Coq_ty.Coq_unit
          (RiscvPmpProgram.coq_FunDef Coq_ctx.Coq_nil Coq_ty.Coq_unit
            RiscvPmpProgram.Coq_step)
          w1)
        Coq_env.Coq_nil)
      (fun w2 _UU03b8_2 _ ->
      RiscvPmpSignature.SHeapSpec.bind w2
        (RiscvPmpSignature.SHeapSpec.angelic None w2 RiscvPmpBase.ty_xlenbits)
        (fun w3 _UU03b8_3 na ->
        let a3 =
          RiscvPmpSignature.persist
            (RiscvPmpSignature.persistent_subst
              (RiscvPmpBase.coq_SubstTerm RiscvPmpBase.ty_xlenbits))
            w a w3
            (RiscvPmpSignature.acc_trans w w2 w3
              (RiscvPmpSignature.acc_trans w w1 w2 _UU03b8_1 _UU03b8_2)
              _UU03b8_3)
        in
        RiscvPmpSignature.SHeapSpec.bind w3
          (RiscvPmpSignature.SHeapSpec.consume (Coq_ctx.Coq_snoc
            ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
            (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
              Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
              EmptyString)));
            Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
            (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
              Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
              ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
              Coq_true, Coq_true, Coq_false)), EmptyString)))));
            Binding.coq_type = RiscvPmpBase.ty_xlenbits }))
            (exec_instruction_epilogue i) w3 (Coq_env.Coq_snoc
            ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
            (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
              Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
              EmptyString)));
            Binding.coq_type = RiscvPmpBase.ty_xlenbits })),
            (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
            { Binding.name =
            (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
              Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
              EmptyString)));
            Binding.coq_type = RiscvPmpBase.ty_xlenbits }, a3)),
            { Binding.name =
            (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
              Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
              ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
              Coq_true, Coq_true, Coq_false)), EmptyString)))));
            Binding.coq_type = RiscvPmpBase.ty_xlenbits }, na)))
          (fun w4 _UU03b8_4 _ ->
          RiscvPmpSignature.SHeapSpec.pure w4
            (RiscvPmpSignature.persist
              (RiscvPmpSignature.persistent_subst
                (RiscvPmpBase.coq_SubstTerm RiscvPmpBase.ty_xlenbits))
              w3 na w4 _UU03b8_4))))))

(** val sexec_block_addr :
    coq_AST list -> (RiscvPmpBase.coq_Term, (RiscvPmpBase.coq_Term,
    RiscvPmpBase.coq_Term RiscvPmpSignature.coq_SHeapSpec)
    RiscvPmpSignature.coq_Impl) RiscvPmpSignature.coq_Impl
    RiscvPmpSignature.coq_Valid **)

let rec sexec_block_addr b w ainstr apc =
  match b with
  | [] -> RiscvPmpSignature.SHeapSpec.pure w apc
  | i::b' ->
    RiscvPmpSignature.SHeapSpec.bind w
      (RiscvPmpSignature.SHeapSpec.assert_formula w (fun _ ->
        RiscvPmpBase.Coq_amsg.empty w.RiscvPmpSignature.wctx)
        (RiscvPmpSignature.Coq_formula_relop (RiscvPmpBase.ty_xlenbits,
        (Coq_bop.Coq_eq RiscvPmpBase.ty_xlenbits), ainstr, apc)))
      (fun w1 _UU03b8_1 _ ->
      RiscvPmpSignature.SHeapSpec.bind w1
        (sexec_instruction i w1
          (RiscvPmpSignature.persist
            (RiscvPmpSignature.persistent_subst
              (RiscvPmpBase.coq_SubstTerm RiscvPmpBase.ty_xlenbits))
            w apc w1 _UU03b8_1))
        (fun w2 _UU03b8_2 apc' ->
        sexec_block_addr b' w2 (RiscvPmpBase.Coq_term_binop ((Coq_ty.Coq_bvec
          xlenbits), (Coq_ty.Coq_bvec xlenbits), (Coq_ty.Coq_bvec xlenbits),
          (Coq_bop.Coq_bvadd xlenbits),
          (RiscvPmpSignature.persist
            (RiscvPmpSignature.persistent_subst
              (RiscvPmpBase.coq_SubstTerm RiscvPmpBase.ty_xlenbits))
            w ainstr w2
            (RiscvPmpSignature.acc_trans w w1 w2 _UU03b8_1 _UU03b8_2)),
          (RiscvPmpBase.Coq_term_val (RiscvPmpBase.ty_word,
          (Obj.magic bv_instrsize word))))) apc'))

(** val sexec_triple_addr :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpSignature.Coq_asn.coq_Assertion -> coq_AST list ->
    RiscvPmpSignature.Coq_asn.coq_Assertion -> RiscvPmpBase.coq_Unit
    RiscvPmpSignature.coq_SHeapSpec RiscvPmpSignature.coq_Valid **)

let sexec_triple_addr _UU03a3_ req b ens w =
  RiscvPmpSignature.SHeapSpec.bind w
    (RiscvPmpSignature.SHeapSpec.demonic_ctx (Obj.magic id) w
      (Obj.magic _UU03a3_))
    (fun w1 _ _UU03b4_ ->
    RiscvPmpSignature.SHeapSpec.bind w1
      (RiscvPmpSignature.SHeapSpec.demonic (Some
        (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
          Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
          EmptyString))))
        w1 RiscvPmpBase.ty_xlenbits)
      (fun w2 _UU03b8_1 a ->
      let _UU03b4_1 = Coq_env.Coq_snoc ((Obj.magic _UU03a3_),
        (RiscvPmpSignature.persist
          (RiscvPmpSignature.persistent_subst
            (Obj.magic RiscvPmpBase.subst_localstore _UU03a3_))
          w1 _UU03b4_ w2 _UU03b8_1),
        { Binding.name = (String ((Ascii (Coq_true, Coq_false, Coq_false,
        Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), EmptyString));
        Binding.coq_type = RiscvPmpBase.ty_xlenbits }, a)
      in
      RiscvPmpSignature.SHeapSpec.bind w2
        (RiscvPmpSignature.SHeapSpec.produce (Coq_ctx.Coq_snoc (_UU03a3_,
          { Binding.name =
          (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
            Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
            EmptyString)));
          Binding.coq_type = RiscvPmpBase.ty_xlenbits })) req w2
          (Obj.magic _UU03b4_1))
        (fun w3 _UU03b8_2 _ ->
        let a2 =
          RiscvPmpSignature.persist
            (RiscvPmpSignature.persistent_subst
              (RiscvPmpBase.coq_SubstTerm RiscvPmpBase.ty_xlenbits))
            w2 a w3 _UU03b8_2
        in
        RiscvPmpSignature.SHeapSpec.bind w3 (sexec_block_addr b w3 a2 a2)
          (fun w4 _UU03b8_3 na ->
          let _UU03b4_3 =
            RiscvPmpSignature.persist
              (RiscvPmpSignature.persistent_subst
                (Obj.magic RiscvPmpBase.subst_localstore (Coq_ctx.Coq_snoc
                  (_UU03a3_, { Binding.name =
                  (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
                    Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
                    EmptyString)));
                  Binding.coq_type = RiscvPmpBase.ty_xlenbits }))))
              w2 _UU03b4_1 w4
              (RiscvPmpSignature.acc_trans w2 w3 w4 _UU03b8_2 _UU03b8_3)
          in
          RiscvPmpSignature.SHeapSpec.consume (Coq_ctx.Coq_snoc
            ((Coq_ctx.Coq_snoc (_UU03a3_, { Binding.name =
            (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
              Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
              EmptyString)));
            Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
            (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
              Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
              ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
              Coq_true, Coq_true, Coq_false)), EmptyString)))));
            Binding.coq_type = RiscvPmpBase.ty_xlenbits })) ens w4
            (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc (_UU03a3_, { Binding.name =
            (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
              Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
              EmptyString)));
            Binding.coq_type = RiscvPmpBase.ty_xlenbits })),
            (Obj.magic _UU03b4_3), { Binding.name =
            (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
              Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
              ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
              Coq_true, Coq_true, Coq_false)), EmptyString)))));
            Binding.coq_type = RiscvPmpBase.ty_xlenbits }, na))))))

(** val sblock_verification_condition :
    (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
    RiscvPmpSignature.Coq_asn.coq_Assertion -> coq_AST list ->
    RiscvPmpSignature.Coq_asn.coq_Assertion ->
    RiscvPmpSignature.SymProp.coq_SymProp RiscvPmpSignature.coq_Valid **)

let sblock_verification_condition _UU03a3_ req b ens w =
  RiscvPmpSignature.SHeapSpec.run w (sexec_triple_addr _UU03a3_ req b ens w)
