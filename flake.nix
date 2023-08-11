{
  description = "ouroboros-network";

  inputs = {
    haskellNix.url = "github:input-output-hk/haskell.nix";
    nixpkgs.follows = "haskellNix/nixpkgs-unstable";
    iohkNix.url = "github:input-output-hk/iohk-nix";
    flake-utils.url = "github:hamishmack/flake-utils/hkm/nested-hydraJobs";

    CHaP.url = "github:input-output-hk/cardano-haskell-packages?ref=repo";
    CHaP.flake = false;
  };

  outputs = inputs: let
    supportedSystems = [
      "x86_64-linux"
      "x86_64-darwin"
      "aarch64-darwin"
    ];
  in
    {inherit (inputs);}
    // inputs.flake-utils.lib.eachSystem supportedSystems (
      system: let
        # setup our nixpkgs with the haskell.nix overlays, and the iohk-nix
        # overlays...
        nixpkgs = import inputs.nixpkgs {
          overlays = [
            # haskellNix.overlay can be configured by later overlays, so need to come before them.
            inputs.haskellNix.overlay
          ];
          inherit system;
          inherit (inputs.haskellNix) config;
        };
        inherit (nixpkgs) lib;
        haskellNix = import inputs.haskellNix { };

        # see flake `variants` below for alternative compilers
        defaultCompiler = "ghc8107";
        # We use cabalProject' to ensure we don't build the plan for
        # all systems.
        cabalProject = nixpkgs.haskell-nix.cabalProject' ({config, pkgs, ...}: {
          # pkgs - nixpkgs instatiated for cross compilation, so
          # stdenv.hostPlatform.isWindows will work as expected
          src = ./.;
          name = "ouroboros-network";
          compiler-nix-name = lib.mkDefault defaultCompiler;
          cabalProjectLocal = if pkgs.stdenv.hostPlatform.isWindows
                              then lib.readFile ./scripts/ci/cabal.project.local.Windows.CrossCompile
                              else lib.readFile ./scripts/ci/cabal.project.local.Linux;

          # we also want cross compilation to windows on linux (and only with default compiler).
          crossPlatforms = p:
            lib.optionals nixpkgs.stdenv.hostPlatform.isLinux [p.mingwW64];
            # lib.optional (system == "x86_64-linux" && config.compiler-nix-name == defaultCompiler)
            # p.mingwW64;

          # CHaP input map, so we can find CHaP packages (needs to be more
          # recent than the index-state we set!). Can be updated with
          #
          #  nix flake lock --update-input CHaP
          #
          inputMap = {
            "https://input-output-hk.github.io/cardano-haskell-packages" = inputs.CHaP;
          };
          # tools we want in our shell, from hackage
          shell.tools =
            {
              cabal = "3.10.1.0";
              ghcid = "0.8.8";
            }
            // lib.optionalAttrs (config.compiler-nix-name == defaultCompiler) {
              # tools that work only with default compiler
              stylish-haskell =
                { version = "0.14.4.0";
                  # GHC-8.10.7 requires:
                  cabalProjectLocal = "allow-older: ghc-lib-parser:base";
                };
              # TODO: haskell-language-server doesn't build with `ghc-8.10.7` (a
              # dependency fails to build)
              #haskell-language-server = "2.0.0.1";
            };
          # and from nixpkgs or other inputs
          shell.nativeBuildInputs = with nixpkgs; [ gh jq ];
          # disable Hoogle until someone request it
          shell.withHoogle = false;
          # Skip cross compilers for the shell
          shell.crossPlatforms = _: [];

          # package customizations as needed. Where cabal.project is not
          # specific enough, or doesn't allow setting these.
          modules = [
            ({pkgs, ...}: {
              # pkgs are instatiated for the host platform
              packages.ouroboros-network-protocols.components.tests.cddl.build-tools = [ pkgs.cddl pkgs.cbor-diag ];
              packages.ouroboros-network-protocols.components.tests.cddl.preCheck    = "export HOME=`pwd`";
            })
          ];
        });
        # ... and construct a flake from the cabal project
        flake = cabalProject.flake (
          lib.optionalAttrs (system == "x86_64-linux") {
            # on linux, build/test other supported compilers
            variants = lib.genAttrs ["ghc8107"] (compiler-nix-name: {
              inherit compiler-nix-name;
            });
          }
        );
        network-docs = nixpkgs.callPackage ./nix/network-docs.nix { };
        check-stylish = nixpkgs.callPackage ./nix/check-stylish.nix { };
      in
        lib.recursiveUpdate flake rec {
          project = cabalProject;
          # add a required job, that's basically all hydraJobs.
          hydraJobs =
            nixpkgs.callPackages inputs.iohkNix.utils.ciJobsAggregates
            {
              ciJobs =
                flake.hydraJobs
                // {
                  # This ensure hydra send a status for the required job (even if no change other than commit hash)
                  revision = nixpkgs.writeText "revision" (inputs.self.rev or "dirty");
                  inherit network-docs check-stylish;
                };
            };
          legacyPackages = rec {
            inherit cabalProject nixpkgs;
            # also provide hydraJobs through legacyPackages to allow building without system prefix:
            inherit hydraJobs;
            inherit network-docs check-stylish;
          };
          devShells = let
            profillingShell = p: {
              # `nix develop .#profiling` (or `.#ghc8107.profiling): a shell with profiling enabled
              profiling = (p.appendModule {modules = [{enableLibraryProfiling = true;}];}).shell;
            };
          in
            profillingShell cabalProject
            # Additional shells for every GHC version supported by haskell.nix, eg. `nix develop .#ghc927`
            // lib.mapAttrs (compiler-nix-name: _: let
              p = cabalProject.appendModule {inherit compiler-nix-name;};
            in
              p.shell // (profillingShell p))
            nixpkgs.haskell-nix.compiler;
          # formatter used by nix fmt
          formatter = nixpkgs.alejandra;
        }
    );

  nixConfig = {
    extra-substituters = [
      "https://cache.iog.io"
    ];
    extra-trusted-public-keys = [
      "hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ="
    ];
    allow-import-from-derivation = true;
  };
}
