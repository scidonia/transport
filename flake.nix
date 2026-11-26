{
  description = "transport — type-preserving supercompilation for MLTT";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs =
    { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
    in
    {
      devShells = forAllSystems (
        pkgs:
        let
          # `leanPackages.lean4` is the Lean whose Lake treats a `/nix/store`
          # package directory as up to date; `pkgs.lean4` does not carry that
          # patch.  This project has no Lean dependencies, so no package
          # overrides are needed, but the toolchain must match
          # `lean-toolchain`.
          lean = if pkgs ? leanPackages then pkgs.leanPackages.lean4 else pkgs.lean4;
        in
        {
          default = pkgs.mkShell {
            name = "transport";
            packages = [
              lean
              pkgs.git
              pkgs.coreutils
              pkgs.gnugrep
              pkgs.gnused
              pkgs.gawk
              pkgs.findutils
              pkgs.jq
              pkgs.python3
              pkgs.time
            ];
            shellHook = ''
              unset -f lake lean
              export PATH=${lean}/bin:$PATH
              export LAKE_NO_CACHE=1
              printf 'transport: %s\n' "$(lean --version)"
            '';
          };

          # The HoTT stage reuses the Cubical Agda library rather than
          # axiomatising univalence over Lean's proof-irrelevant `Eq`.
          cubical = pkgs.mkShell {
            name = "transport-cubical";
            packages = [
              (pkgs.agda.withPackages (ps: [ ps.cubical ]))
              pkgs.git
            ];
            shellHook = ''
              printf 'transport-cubical: %s\n' "$(agda --version)"
            '';
          };
        }
      );
    };
}
