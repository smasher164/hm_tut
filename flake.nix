{
  description = "A flake that sets up the devShell with ocaml 5.";
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    let supportedSystems = [ "aarch64-linux" "i686-linux" "x86_64-linux" "aarch64-darwin" ];
    in flake-utils.lib.eachSystem supportedSystems (system:
      let
        pkgs = import nixpkgs {
          inherit system;
        };
      in {
        devShell = pkgs.mkShell {
          buildInputs = with pkgs.ocamlPackages; [
            ocaml
            ocaml-lsp
            dune_3
            odoc
            utop
            findlib
            ppx_inline_test
            base
          ];
        };
      });
}
