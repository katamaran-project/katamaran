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
          _self: super:
            pkgs.lib.foldlAttrs
              # foldAttrs is used to iterate over the versions set and apply a function
              # to each attribute. This function takes three arguments: the accumulator set,
              # the attribute name (package name), and the attribute value (version).
              (acc: pkg: version:
                # This function returns a new set with the current attribute added to the
                # accumulator set. The attribute name is the package name, and the value
                # is the overridden package.
                acc // { ${pkg} = super.${pkg}.override { inherit version; }; })
              # The initial value of the accumulator set.
              { }
              # The attribute set to iterate over.
              versions
        );

      iris41 = {
        iris = "4.1.0";
        stdpp = "1.9.0";
      };

      iris42 = {
        iris = "4.2.0";
        stdpp = "1.10.0";
      };

      coqPackages817 = with (patchCoqPackages pkgs.coqPackages_8_17 iris41); [ coq equations stdpp iris ];
      coqPackages818 = with (patchCoqPackages pkgs.coqPackages_8_18 iris41); [ coq equations stdpp iris ];
      coqPackages819 = with (patchCoqPackages pkgs.coqPackages_8_19 iris42); [ coq equations stdpp iris ];

      emacsPackage = (pkgs.emacsPackagesFor pkgs.emacs).emacsWithPackages (ep:
        with ep; [ company-coq magit proof-general ]);
    in
    {
      devShells = rec {
        default = coq817;
        coq817 = pkgs.mkShell { buildInputs = coqPackages817; };
        coq818 = pkgs.mkShell { buildInputs = coqPackages818; };
        coq819 = pkgs.mkShell { buildInputs = coqPackages819; };

        emacs817 = pkgs.mkShell { buildInputs = coqPackages817 ++ [ emacsPackage ]; };
        emacs818 = pkgs.mkShell { buildInputs = coqPackages818 ++ [ emacsPackage ]; };
        emacs819 = pkgs.mkShell { buildInputs = coqPackages819 ++ [ emacsPackage ]; };
      };
    }
  );
}
