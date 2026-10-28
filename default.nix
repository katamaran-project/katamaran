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
, zstd
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
  # Only the build inputs, so edits to docs or scripts don't force a rebuild.
  src = lib.fileset.toSource {
    root = ./.;
    fileset = lib.fileset.unions [
      ./_CoqProject
      ./Makefile
      ./Makefile.coq.local-late
      ./theories
      ./case_study
      ./examples
      ./test
    ];
  };
  nativeBuildInputs = [ time zstd ];
  buildFlags = [
    "COQMAKE_ONE_TIME_FILE=${make-one-time-file}"
    "TIMING=1"
    "pretty-timed"
  ];
  # Raw timings and build environment, for processing elsewhere.
  outputs = [ "out" "timing" ];
  postInstall = ''
    mkdir -p $timing
    cp time-of-build.log time-of-build-pretty.log $timing/
    find . -name '*.v.timing' -printf '%P\0' \
      | tar -I "zstd -19 -T$NIX_BUILD_CORES" -cf $timing/sentences.tar.zst --null -T -
    {
      echo "rocq_version: $(rocq --version | head -n1)"
      echo "rocq: $(realpath "$(command -v rocq)")"
      echo "ROCQPATH: ''${ROCQPATH-}"
      echo "COQPATH: ''${COQPATH-}"
      echo "jobs: $NIX_BUILD_CORES"
      echo "nproc: $(nproc)"
      echo "cpu: $(grep -m1 '^model name' /proc/cpuinfo | cut -d: -f2- | sed 's/^ *//')"
    } > $timing/env.txt
  '';
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
