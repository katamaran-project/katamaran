{ lib
, mkCoqDerivation
, coq
, equations
, iris
, stdlib
, stdpp
, python3
, time
, writeShellScript
, ...
}:

let
  make-one-time-file = writeShellScript "make-one-time-file" ''
    exec ${python3}/bin/python3 ${coq}/lib/coq-core/tools/make-one-time-file.py "$@"
  '';
in

mkCoqDerivation {
  pname = "katamaran";
  owner = "katamaran-project";
  version = "0.2.0";
  src = ./.;
  nativeBuildInputs = [ time ];
  buildFlags = [
    "COQMAKE_ONE_TIME_FILE=${make-one-time-file}"
    "pretty-timed"
  ];
  propagatedBuildInputs = [
    equations
    iris
    stdlib
    stdpp
  ];
  meta = {
    description = "Separation logic-based verification of instruction sets";
    license = lib.licenses.bsd2;
  };
}
