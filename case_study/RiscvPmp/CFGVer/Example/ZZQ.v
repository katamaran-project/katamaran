(* THROWAWAY: concrete-base twin of zzn, for the parametric-vs-concrete A/B. *)
From Katamaran Require Export RiscvPmp.CFGVer.Example.ZZCommon.

Definition zzc_reg_specs (n : nat) : list reg_spec :=
  [(A0, false, None); (A1, false, None); (A2, false, None);
   (A3, false, Some (bv.of_N 56));
   (A4, true, Some (bv.of_N (N.of_nat n)))].

Definition zzc_mem_specs (n : nat) : list mem_full_spec :=
  List.map (fun k => (bv.of_N (56 + 4 * N.of_nat k), false, @None (Val ty_xlenbits)))
           (List.seq 0 n).

Definition zzc_contract (n : nat) : CFGVerifierContract :=
  gen_contract 0 (zzc_reg_specs n) (zzc_mem_specs n)
    zzn_instrs [] (pcOutOfInstrs_exitCond 0 zzn_instrs) (14 * n + 12).
