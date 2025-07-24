{ lib
, mkCoqDerivation
, coq
, rocq-core
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
  coq-tools-path =
    if lib.versionOlder coq.version "9.0.0"
    then "${coq}/lib/coq-core/tools"
    else "${rocq-core}/lib/rocq-runtime/tools";

  # The python shebang in make-one-time-file.py is unpatched in nixpkgs, so
  # we create a wrapper ourselves to find the right python3. Simply passing
  # python3 as a nativeBuildInput does not work, since the nix sandbox does
  # not contain /usr/bin/env.
  make-one-time-file = writeShellScript "make-one-time-file" ''
    exec ${python3}/bin/python3 ${coq-tools-path}/make-one-time-file.py "$@"
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
    coq.ocamlPackages.findlib
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
