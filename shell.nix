
let
    pkgs = import <nixpkgs> {};
in 
    pkgs.stdenv.mkDerivation {
        name = "crdts";
        buildInputs = [
            pkgs.cargo
            pkgs.rustc
            pkgs.rustfmt
            pkgs.clippy
            pkgs.rls
        ];
    }
