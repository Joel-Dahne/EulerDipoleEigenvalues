{
  description = "Development shell for building the blueprint";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05";

  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
    in
    {
      # Only provides leanblueprint. Building the blueprint also needs TeX
      # (xelatex and latexmk for the pdf; kpsewhich, which plasTeX uses to find
      # \input files, for the web version), which is expected on the host.
      devShells = forAllSystems (pkgs: {
        default = pkgs.mkShell {
          packages = [
            # leanblueprint runs plasTeX in a subprocess, so both must come from
            # one Python environment that also contains the plasTeX plugins.
            (pkgs.python3.withPackages (ps: [ ps.leanblueprint ]))
          ];
        };
      });
    };
}
