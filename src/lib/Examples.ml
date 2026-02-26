open Ascii
open Base1
open BinOps
open Bitvector
open Context
open Datatypes
open Environment
open PartialVerifier
open Sig
open String
open TypeDecl
open Variables

module Examples =
 struct
  (** val minimal_pre :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpSignature.Coq_asn.coq_Assertion **)

  let minimal_pre _UU03a3_ =
    RiscvPmpSignature.Coq_asn.Coq_sep ((RiscvPmpSignature.Coq_asn.Coq_chunk
      (RiscvPmpSignature.Coq_chunk_ptsreg (RiscvPmpBase.ty_privilege,
      RiscvPmpBase.Coq_cur_privilege, (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_privilege, (Obj.magic Machine)))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_chunk
      (RiscvPmpSignature.Coq_chunk_ptsreg (RiscvPmpBase.ty_mstatus,
      RiscvPmpBase.Coq_mstatus, (RiscvPmpBase.Coq_term_record
      ((Obj.magic Coq_rmstatus), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)),
        EmptyString)))))));
      Binding.coq_type = RiscvPmpBase.ty_privilege })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_false)), EmptyString)))))))));
      Binding.coq_type = Coq_ty.Coq_bool })), (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)),
        EmptyString)))))));
      Binding.coq_type = RiscvPmpBase.ty_privilege })), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)),
        EmptyString)))))));
      Binding.coq_type = RiscvPmpBase.ty_privilege },
      (RiscvPmpBase.Coq_term_val (RiscvPmpBase.ty_privilege,
      (Obj.magic User))))), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_false)), EmptyString)))))))));
      Binding.coq_type = Coq_ty.Coq_bool }, (RiscvPmpBase.Coq_term_val
      (Coq_ty.Coq_bool, (Obj.magic Coq_false))))), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_false, Coq_true, Coq_false)),
        EmptyString)))))));
      Binding.coq_type = Coq_ty.Coq_bool }, (RiscvPmpBase.Coq_term_val
      (Coq_ty.Coq_bool, (Obj.magic Coq_false)))))))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_exist
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))),
      RiscvPmpBase.ty_Minterrupts, (RiscvPmpSignature.Coq_asn.Coq_chunk
      (RiscvPmpSignature.Coq_chunk_ptsreg (RiscvPmpBase.ty_Minterrupts,
      RiscvPmpBase.Coq_mip, (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))),
      RiscvPmpBase.ty_Minterrupts, O))))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_exist
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))),
      RiscvPmpBase.ty_Minterrupts, (RiscvPmpSignature.Coq_asn.Coq_chunk
      (RiscvPmpSignature.Coq_chunk_ptsreg (RiscvPmpBase.ty_Minterrupts,
      RiscvPmpBase.Coq_mie, (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))),
      RiscvPmpBase.ty_Minterrupts, O))))))),
      (RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
      (Coq_pmp_entries, (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry),
      (RiscvPmpBase.term_list _UU03a3_ (Coq_ty.Coq_prod
        (RiscvPmpBase.ty_pmpcfg_ent, RiscvPmpBase.ty_xlenbits)) (Coq_cons
        ((RiscvPmpBase.Coq_term_binop (RiscvPmpBase.ty_pmpcfg_ent,
        RiscvPmpBase.ty_xlenbits, (Coq_ty.Coq_prod
        (RiscvPmpBase.ty_pmpcfg_ent, RiscvPmpBase.ty_xlenbits)),
        (Coq_bop.Coq_pair (RiscvPmpBase.ty_pmpcfg_ent,
        RiscvPmpBase.ty_xlenbits)), (RiscvPmpBase.Coq_term_val
        (RiscvPmpBase.ty_pmpcfg_ent,
        (Obj.magic RiscvPmpSignature.default_pmpcfg_ent))),
        (RiscvPmpBase.Coq_term_val (RiscvPmpBase.ty_xlenbits,
        (Obj.magic Coq_bv.zero xlenbits))))), (Coq_cons
        ((RiscvPmpBase.Coq_term_binop (RiscvPmpBase.ty_pmpcfg_ent,
        RiscvPmpBase.ty_xlenbits, (Coq_ty.Coq_prod
        (RiscvPmpBase.ty_pmpcfg_ent, RiscvPmpBase.ty_xlenbits)),
        (Coq_bop.Coq_pair (RiscvPmpBase.ty_pmpcfg_ent,
        RiscvPmpBase.ty_xlenbits)), (RiscvPmpBase.Coq_term_val
        (RiscvPmpBase.ty_pmpcfg_ent,
        (Obj.magic RiscvPmpSignature.default_pmpcfg_ent))),
        (RiscvPmpBase.Coq_term_val (RiscvPmpBase.ty_xlenbits,
        (Obj.magic Coq_bv.zero xlenbits))))), Coq_nil)))))))))))))))))

  (** val minimal_post :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpSignature.Coq_asn.coq_Assertion **)

  let minimal_post _UU03a3_ =
    RiscvPmpSignature.Coq_asn.Coq_sep ((RiscvPmpSignature.Coq_asn.Coq_chunk
      (RiscvPmpSignature.Coq_chunk_ptsreg (RiscvPmpBase.ty_privilege,
      RiscvPmpBase.Coq_cur_privilege, (RiscvPmpBase.Coq_term_val
      (RiscvPmpBase.ty_privilege, (Obj.magic Machine)))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_chunk
      (RiscvPmpSignature.Coq_chunk_ptsreg (RiscvPmpBase.ty_mstatus,
      RiscvPmpBase.Coq_mstatus, (RiscvPmpBase.Coq_term_record
      ((Obj.magic Coq_rmstatus), (Coq_env.Coq_snoc ((Coq_ctx.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)),
        EmptyString)))))));
      Binding.coq_type = RiscvPmpBase.ty_privilege })), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_false)), EmptyString)))))))));
      Binding.coq_type = Coq_ty.Coq_bool })), (Coq_env.Coq_snoc
      ((Coq_ctx.Coq_snoc (Coq_ctx.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)),
        EmptyString)))))));
      Binding.coq_type = RiscvPmpBase.ty_privilege })), (Coq_env.Coq_snoc
      (Coq_ctx.Coq_nil, Coq_env.Coq_nil, { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
        Coq_false, Coq_false, Coq_true, Coq_false, Coq_true, Coq_false)),
        EmptyString)))))));
      Binding.coq_type = RiscvPmpBase.ty_privilege },
      (RiscvPmpBase.Coq_term_val (RiscvPmpBase.ty_privilege,
      (Obj.magic User))))), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false)), (String ((Ascii
        (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true, Coq_false,
        Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
        Coq_false, Coq_true, Coq_false, Coq_false, Coq_true, Coq_false)),
        (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_false, Coq_true, Coq_false)), EmptyString)))))))));
      Binding.coq_type = Coq_ty.Coq_bool }, (RiscvPmpBase.Coq_term_val
      (Coq_ty.Coq_bool, (Obj.magic Coq_false))))), { Binding.name =
      (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
        Coq_false, Coq_false, Coq_true, Coq_false)), (String ((Ascii
        (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_false,
        Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
        Coq_true, Coq_false, Coq_false, Coq_false, Coq_true, Coq_false)),
        EmptyString)))))));
      Binding.coq_type = Coq_ty.Coq_bool }, (RiscvPmpBase.Coq_term_val
      (Coq_ty.Coq_bool, (Obj.magic Coq_false)))))))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_exist
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))),
      RiscvPmpBase.ty_Minterrupts, (RiscvPmpSignature.Coq_asn.Coq_chunk
      (RiscvPmpSignature.Coq_chunk_ptsreg (RiscvPmpBase.ty_Minterrupts,
      RiscvPmpBase.Coq_mip, (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_false, Coq_false,
         Coq_false, Coq_false, Coq_true, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))),
      RiscvPmpBase.ty_Minterrupts, O))))))),
      (RiscvPmpSignature.Coq_asn.Coq_sep
      ((RiscvPmpSignature.Coq_asn.Coq_exist
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))),
      RiscvPmpBase.ty_Minterrupts, (RiscvPmpSignature.Coq_asn.Coq_chunk
      (RiscvPmpSignature.Coq_chunk_ptsreg (RiscvPmpBase.ty_Minterrupts,
      RiscvPmpBase.Coq_mie, (RiscvPmpBase.Coq_term_var
      ((Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
         Coq_false, Coq_true, Coq_true, Coq_false)), (String ((Ascii
         (Coq_true, Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
         Coq_true, Coq_false)), (String ((Ascii (Coq_true, Coq_false,
         Coq_true, Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
         EmptyString))))))),
      RiscvPmpBase.ty_Minterrupts, O))))))),
      (RiscvPmpSignature.Coq_asn.Coq_chunk (RiscvPmpSignature.Coq_chunk_user
      (Coq_pmp_entries, (Coq_env.Coq_snoc (Coq_ctx.Coq_nil, Coq_env.Coq_nil,
      (Coq_ty.Coq_list RiscvPmpBase.ty_pmpentry),
      (RiscvPmpBase.term_list _UU03a3_ (Coq_ty.Coq_prod
        (RiscvPmpBase.ty_pmpcfg_ent, RiscvPmpBase.ty_xlenbits)) (Coq_cons
        ((RiscvPmpBase.Coq_term_binop (RiscvPmpBase.ty_pmpcfg_ent,
        RiscvPmpBase.ty_xlenbits, (Coq_ty.Coq_prod
        (RiscvPmpBase.ty_pmpcfg_ent, RiscvPmpBase.ty_xlenbits)),
        (Coq_bop.Coq_pair (RiscvPmpBase.ty_pmpcfg_ent,
        RiscvPmpBase.ty_xlenbits)), (RiscvPmpBase.Coq_term_val
        (RiscvPmpBase.ty_pmpcfg_ent,
        (Obj.magic RiscvPmpSignature.default_pmpcfg_ent))),
        (RiscvPmpBase.Coq_term_val (RiscvPmpBase.ty_xlenbits,
        (Obj.magic Coq_bv.zero xlenbits))))), (Coq_cons
        ((RiscvPmpBase.Coq_term_binop (RiscvPmpBase.ty_pmpcfg_ent,
        RiscvPmpBase.ty_xlenbits, (Coq_ty.Coq_prod
        (RiscvPmpBase.ty_pmpcfg_ent, RiscvPmpBase.ty_xlenbits)),
        (Coq_bop.Coq_pair (RiscvPmpBase.ty_pmpcfg_ent,
        RiscvPmpBase.ty_xlenbits)), (RiscvPmpBase.Coq_term_val
        (RiscvPmpBase.ty_pmpcfg_ent,
        (Obj.magic RiscvPmpSignature.default_pmpcfg_ent))),
        (RiscvPmpBase.Coq_term_val (RiscvPmpBase.ty_xlenbits,
        (Obj.magic Coq_bv.zero xlenbits))))), Coq_nil)))))))))))))))))

  (** val extend_to_minimal_pre :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpSignature.Coq_asn.coq_Assertion ->
      RiscvPmpSignature.Coq_asn.coq_Assertion **)

  let extend_to_minimal_pre _UU03a3_ p =
    RiscvPmpSignature.Coq_asn.Coq_sep (p, (minimal_pre _UU03a3_))

  (** val extend_to_minimal_post :
      (coq_LVar, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpSignature.Coq_asn.coq_Assertion ->
      RiscvPmpSignature.Coq_asn.coq_Assertion **)

  let extend_to_minimal_post _UU03a3_ q =
    RiscvPmpSignature.Coq_asn.Coq_sep (q, (minimal_post _UU03a3_))

  (** val coq_VC_triple :
      (string, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      RiscvPmpSignature.Coq_asn.coq_Assertion -> coq_AST list ->
      RiscvPmpSignature.Coq_asn.coq_Assertion ->
      RiscvPmpSignature.SymProp.coq_SymProp **)

  let coq_VC_triple _UU03a3_ p i q =
    sblock_verification_condition (Obj.magic _UU03a3_)
      (extend_to_minimal_pre (Coq_ctx.Coq_snoc ((Obj.magic _UU03a3_),
        { Binding.name =
        (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
          Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
          EmptyString)));
        Binding.coq_type = RiscvPmpBase.ty_xlenbits })) p)
      i
      (extend_to_minimal_post (Coq_ctx.Coq_snoc ((Coq_ctx.Coq_snoc
        ((Obj.magic _UU03a3_), { Binding.name =
        (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
          Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)),
          EmptyString)));
        Binding.coq_type = RiscvPmpBase.ty_xlenbits })), { Binding.name =
        (Obj.magic (String ((Ascii (Coq_true, Coq_false, Coq_false,
          Coq_false, Coq_false, Coq_true, Coq_true, Coq_false)), (String
          ((Ascii (Coq_false, Coq_true, Coq_true, Coq_true, Coq_false,
          Coq_true, Coq_true, Coq_false)), EmptyString)))));
        Binding.coq_type = RiscvPmpBase.ty_xlenbits })) q)
      RiscvPmpSignature.wnil

  type coq_BlockVerifierContract = { precondition : RiscvPmpSignature.Coq_asn.coq_Assertion;
                                     instrs : coq_AST list;
                                     postcondition : RiscvPmpSignature.Coq_asn.coq_Assertion }

  (** val exec_VC :
      (string, Coq_ty.coq_Ty) Binding.coq_Binding Coq_ctx.coq_Ctx ->
      coq_BlockVerifierContract -> RiscvPmpSignature.SymProp.coq_SymProp **)

  let exec_VC _UU03a3_ c =
    let { precondition = p; instrs = i; postcondition = q } = c in
    RiscvPmpSignature.postprocess2
      RiscvPmpSignature.wnil.RiscvPmpSignature.wctx
      (coq_VC_triple _UU03a3_ p i q)
 end
