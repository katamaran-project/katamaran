
let () = 
  let triple =
    { precondition = _;
      instr = _;
      postcondition = _ }
  in
  let string_of_symprop s = _ in
  let result = BlockVerifier.exec_VC BlockVerifier.Coq_nil triple in
  print_endline (string_of_symprop result)

