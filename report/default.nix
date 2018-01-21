let
  pkgs = import <nixpkgs> {};
in
  with pkgs;
  rec {
    tex = texlive.combine {
      inherit (texlive)
          scheme-full
        ;
    };
  }
