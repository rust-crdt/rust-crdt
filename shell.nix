
let
    pkgs = import <nixpkgs> {};
in 
pkgs.stdenv.mkDerivation {
  name = "crdts";
    buildInputs = [
      (pkgs.rustChannelOf { channel = "stable"; }).rust
    ];
}
