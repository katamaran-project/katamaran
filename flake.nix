{
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = inputs: inputs.flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = import inputs.nixpkgs { inherit system; };
      # Function to override versions of coq packages. This function takes two arguments:
      # - coqPackages: The set of all Coq packages.
      # - versions: An attribute set of packages with their versions we want to override.
      patchCoqPackages = coqPackages: versions:
        coqPackages.overrideScope (
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

      coqPackages819 = patchCoqPackages pkgs.coqPackages_8_19 iris43;
      coqPackages820 = patchCoqPackages pkgs.coqPackages_8_20 iris43;
    in
    {
      packages = rec {
        default = coq819;
        coq819 = coqPackages819.katamaran;
        coq820 = coqPackages820.katamaran;
      };
    }
  );
}
