{
  description = "Metamath Zero specification language";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    naersk = {
      url = "github:nmattia/naersk";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    fenix = {
      url = "github:nix-community/fenix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, naersk, fenix, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        rust-toolchain = fenix.packages.${system}.stable;
        naersk-lib = naersk.lib.${system}.override {
          inherit (rust-toolchain) cargo rustc;
        };
      in rec {
        # `nix build`
        packages.mm0-rs = naersk-lib.buildPackage {
          root = ./mm0-rs;
          singleStep = true;
        };

        packages.mm0-c = pkgs.stdenv.mkDerivation {
          name = "mm0-c";
          src = ./.;
          buildPhase = ''
          cd examples
          mm0-rs compile peano.mm1 peano.mmb
          cd ../mm0-c
          ./make.sh
          '';
          installPhase = ''
            mkdir -p $out/bin
            install -m 755 mm0-c $out/bin
          '';
          buildInputs = [
            self.packages.${system}.mm0-rs
          ];
        };

        defaultPackage = pkgs.symlinkJoin {
          name = "mm0";
          paths = [
            packages.mm0-rs
            packages.mm0-c
          ];
        };

        # `nix run`
        apps.mm0-rs = packages.mm0-rs;
        defaultApp = apps.mm0-rs;

        # `nix develop`
        devShell = pkgs.mkShell {
          buildInputs = [ rust-toolchain.completeToolchain pkgs.rust-analyzer ];
        };
      });
}
