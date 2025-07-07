{
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.05";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = inputs: inputs.flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = import inputs.nixpkgs { inherit system; };
      # Function to override versions of rocq packages. This function takes two arguments:
      # - rocqPackages: The set of all Rocq packages.
      # - versions: An attribute set of packages with their versions we want to override.
      patchRocqPackages = rocqPackages: versions:
        rocqPackages.overrideScope (
          self: super:
            pkgs.lib.foldlAttrs
              # foldAttrs is used to iterate over the versions set and apply a function
              # to each attribute. This function takes three arguments: the accumulator set,
              # the attribute name (package name), and the attribute value (version).
              (acc: pkg: version:
                # This function returns a new set with the current attribute added to the
                # accumulator set. The attribute name is the package name, and the value
                # is the overridden package.
                acc // { ${pkg} = super.${pkg}.override { inherit version; }; })
              # The initial value of the accumulator set. We add our own package here.
              { katamaran = self.callPackage ./default.nix { }; }
              # The attribute set to iterate over.
              versions
        );

      iris43 = {
        iris = "4.3.0";
        stdpp = "1.11.0";
      };

      rocqPackages819 = patchRocqPackages pkgs.coqPackages_8_19 iris43;
      rocqPackages820 = patchRocqPackages pkgs.coqPackages_8_20 iris43;
      rocqPackages900 = patchRocqPackages pkgs.coqPackages_9_0 iris43;

      mkDeps = pkg: pkgs.linkFarmFromDrvs "deps"
        (pkg.buildInputs ++ pkg.nativeBuildInputs ++ pkg.propagatedBuildInputs);
    in
    rec {
      packages = rec {
        default = rocq819;
        rocq819 = rocqPackages819.katamaran;
        rocq820 = rocqPackages820.katamaran;
        rocq900 = rocqPackages900.katamaran;

        rocq819-deps = mkDeps rocq819;
        rocq820-deps = mkDeps rocq820;
        rocq900-deps = mkDeps rocq900;
      };
    }
  );
}
