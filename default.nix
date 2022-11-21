let
  pkgs = import <nixpkgs> { };
  hspkgs = pkgs.haskell.packages.ghc924.override {
    overrides = self: super: rec {
      primdata = pkgs.haskell.packages.ghc924.developPackage {
        root = ../primdata;
        modifier = drv: pkgs.haskell.lib.addBuildTools drv [ pkgs.llvm ];
      };
      dynamic-array = hspkgs.developPackage {
        root = ../dynamic-array;
        modifier = drv: pkgs.haskell.lib.addBuildTools drv [ pkgs.llvm ];
      };
    };
  };
in
  hspkgs.developPackage {
    root = ./.;
    source-overrides = {
      strict-impl-params = ../strict-impl-params;
      flatparse = ../flatparse;
    };
    modifier = drv: pkgs.haskell.lib.overrideCabal drv (old: {
      prePatch = builtins.concatStringsSep "\n" [
        "rm sett.cabal"
        (old.prePatch or "")
      ]; });
  }
