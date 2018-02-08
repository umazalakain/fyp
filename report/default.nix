let
  pkgs = import <nixpkgs> {};
in
  with pkgs;
  {
    inherit xits-math;
    inherit gyre-fonts;
    inherit tex-gyre-schola-math;
    tex = texlive.combine {
      inherit (texlive)
          scheme-full
          polytable
          xits
          latexmk
          tex-gyre
          tex-gyre-math
        ;
    };
  }
