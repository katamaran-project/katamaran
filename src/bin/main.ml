open BlockVerifier

let () =
  let triple =
    { precondition = Coq_formula_true Coq_formula;
      instr = Nil;
      postcondition = Coq_formula_true Coq_formula }
  in
  let string_of_symprop s = "Test" (* stubbed the definition for now... *) in
  let result = exec_VC Coq_nil triple in
  print_endline (string_of_symprop result)
