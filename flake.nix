{
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
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

      iris45 = {
        iris = "4.5.0";
        stdpp = "1.13.0";
      };

      rocqPackages920 = patchRocqPackages pkgs.rocqPackages_9_2 iris45;
      rocqPackages930 = patchRocqPackages pkgs.rocqPackages_9_3 iris45;

      mkDeps = pkg: pkgs.linkFarmFromDrvs "deps"
        (pkg.buildInputs ++ pkg.nativeBuildInputs ++ pkg.propagatedBuildInputs);
    in
    rec {
      packages = rec {
        default = rocq920;
        rocq920 = rocqPackages920.katamaran;
        rocq930 = rocqPackages930.katamaran;

        rocq920-deps = mkDeps rocq920;
        rocq930-deps = mkDeps rocq930;
      };
    }
  );
}
