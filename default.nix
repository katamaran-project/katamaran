{ lib
, mkCoqDerivation
, coq
, equations
, iris
, stdpp
, ...
}:

mkCoqDerivation {
  pname = "katamaran";
  owner = "katamaran-project";
  version = "0.2.0";
  src = ./.;
  propagatedBuildInputs = [
    equations
    iris
    stdpp
  ];
  meta = {
    description = "Separation logic-based verification of instruction sets";
    license = lib.licenses.bsd2;
  };
}
