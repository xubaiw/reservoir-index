{
  description = "LeanPlay";

  inputs = {
    lean = {
      url = github:leanprover/lean4;
    };

    nixpkgs.url = github:nixos/nixpkgs/nixos-21.05;
    flake-utils = {
      url = github:numtide/flake-utils;
      inputs.nixpkgs.follows = "nixpkgs";
    };
    lake = {
      url = github:yatima-inc/lake/acs/add-nix-flake-build;
      inputs.lean.follows = "lean";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    blake3-c.url = github:yatima-inc/BLAKE3/acs/add-flake-setup;
    blake3 = {
      url = github:yatima-inc/lean-blake3;
      inputs.lean.follows = "lean";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.blake3.follows = "blake3-c";
    };
  };

  outputs = { self, lean, flake-utils, nixpkgs, lake, blake3, blake3-c }: flake-utils.lib.eachDefaultSystem (system:
    let
      leanPkgs = lean.packages.${system};
      lakeApps = lake.apps.${system};
      lakePkgs = lake.packages.${system};
      blake3Mod = blake3.project.${system};
      blake3-staticLib = blake3-c.packages.${system}.BLAKE3-c.staticLib;
      lakeExe = lakePkgs.lakeProject.executable;
      pkgs = import nixpkgs { inherit system; };
      name = "LeanPlay";
      cLib = import ./c/default.nix { inherit pkgs; };
      project = leanPkgs.buildLeanPackage {
        inherit name;
        src = ./src;
        deps = [ lakePkgs.lakeProject blake3Mod ];
        debug = true;
        linkFlags = [ blake3-staticLib "-v" ];
        staticLibDeps = [ ];
      };
    in
    {
      packages = {
        inherit project;
        inherit (project) executable modRoot lean-package;
        inherit cLib;
      };

      apps = lakeApps // {
        ${name} = flake-utils.lib.mkApp {
          drv = project.executable;
        };
      };

      defaultApp = self.apps.${system}.${name};

      defaultPackage = project.modRoot;
      devShell = pkgs.mkShell {
        buildInputs = with leanPkgs; [ leanPkgs.lean lakeExe ];
        LEAN_PATH = "${leanPkgs.Lean.modRoot}:${lakePkgs.lakeProject.modRoot}";
        CPATH = "${leanPkgs.Lean.modRoot}";
      };
    });
}
