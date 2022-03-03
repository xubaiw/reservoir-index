{ pkgs }:
let
  libName = "libLeanPlay.a";
  cLib = pkgs.stdenv.mkDerivation {
    name = "LeanPlay-cLib";
    nativeBuildInputs = with pkgs; [ gcc ];
    src = ./.;
    buildPhase = ''
      gcc -o add.o -c ./add.cpp
      ar rcs ${libName} add.o
    '';
    installPhase = ''
      cp ${libName} $out
    '';
  };
in
cLib
