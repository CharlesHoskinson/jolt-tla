{
  description = "Jolt TLA+ Formal Specification - zkVM continuation semantics";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.05";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };

        # TLA+ tools (pinned v1.8.0)
        tla2tools = pkgs.fetchurl {
          url = "https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar";
          sha256 = "sha256-/eogSUB52JsuO3UcY45ipEQ5J3Iu/tYUCKTqKFW0npg=";
        };

      in {
        # === Packages ===
        packages = {
          # TLA+ verification script
          tla-check = pkgs.writeShellScriptBin "jolt-tla-check" ''
            exec ${pkgs.jdk17}/bin/java -XX:+UseParallelGC -Xmx4g \
              -jar ${tla2tools} \
              -config "$1" \
              "$2" \
              -workers auto "''${@:3}"
          '';

          # TLA+ parser
          tla-parse = pkgs.writeShellScriptBin "jolt-tla-parse" ''
            exec ${pkgs.jdk17}/bin/java -cp ${tla2tools} tla2sany.SANY "$@"
          '';

          default = self.packages.${system}.tla-check;
        };

        # === Development Shell ===
        devShells.default = pkgs.mkShell {
          buildInputs = [
            # Lean toolchain (use elan to manage versions)
            pkgs.elan

            # TLA+ verification
            pkgs.jdk17

            # Scripts
            pkgs.python311
            pkgs.bash
            pkgs.git
            pkgs.curl
          ];

          TLAPLUS_JAR = "${tla2tools}";

          shellHook = ''
            echo "jolt-tla development shell"
            echo ""

            # Ensure elan is set up
            if [ ! -f "$HOME/.elan/env" ]; then
              echo "Initializing elan (Lean version manager)..."
              elan default leanprover/lean4:v4.26.0
            fi

            # Source elan environment
            if [ -f "$HOME/.elan/env" ]; then
              . "$HOME/.elan/env"
            fi

            echo "  Lean:  $(lean --version 2>/dev/null || echo 'run: elan default leanprover/lean4:v4.26.0')"
            echo "  Java:  $(java --version 2>&1 | head -1)"
            echo "  TLA+:  v1.8.0 (at \$TLAPLUS_JAR)"
            echo ""
            echo "Commands:"
            echo "  cd lean && lake build      - Build oracle"
            echo "  cd lean && lake exe oracle - Run oracle CLI"
            echo "  cd lean && lake exe test   - Run Lean tests"
            echo "  java -jar \$TLAPLUS_JAR -config Jolt.cfg tla/MC_Jolt.tla -workers auto"
          '';
        };

        # === Checks ===
        # Note: TLA+ parsing check omitted due to SANY path resolution issues in Nix sandbox
        # Use `nix develop` then run: java -jar $TLAPLUS_JAR -config Jolt.cfg tla/MC_Jolt.tla
        checks = { };
      }
    ) // {
      # === NixOS Module ===
      nixosModules.default = { config, lib, pkgs, ... }:
        with lib;
        let
          cfg = config.programs.jolt-tla;
        in {
          options.programs.jolt-tla = {
            enable = mkEnableOption "Jolt TLA+ development tools";
          };

          config = mkIf cfg.enable {
            environment.systemPackages = [
              self.packages.${pkgs.system}.tla-check
              self.packages.${pkgs.system}.tla-parse
              pkgs.elan
              pkgs.jdk17
            ];
          };
        };

      # === Overlay ===
      overlays.default = final: prev: {
        jolt-tla-check = self.packages.${prev.system}.tla-check;
        jolt-tla-parse = self.packages.${prev.system}.tla-parse;
      };
    };
}
