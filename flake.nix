{
  description = "Jolt TLA+ Formal Specification - zkVM continuation semantics";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.05";
    flake-utils.url = "github:numtide/flake-utils";
    lean4-nix = {
      url = "github:lenianiva/lean4-nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, flake-utils, lean4-nix }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };

        # Read Lean version from lean-toolchain (v4.26.0)
        overlay = lean4-nix.readToolchainFile ./lean/lean-toolchain;
        pkgs' = pkgs.extend overlay;

        # lake2nix for pure builds with vendored deps
        lake2nix = lean4-nix.lake { pkgs = pkgs'; };

        # TLA+ tools (pinned v1.8.0)
        tla2tools = pkgs.fetchurl {
          url = "https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar";
          sha256 = "sha256-/eoBlJQ+uZKL9T4z+xfqOPRzEJQU6i/EhQ1NeovX6p4=";
        };

      in {
        # === Packages ===
        packages = {
          # Lean oracle executable
          oracle = lake2nix.mkPackage {
            name = "jolt_oracle";
            src = ./lean;
            lakeTarget = "oracle";
          };

          # TLA+ verification script
          tla-check = pkgs.writeShellScriptBin "jolt-tla-check" ''
            exec ${pkgs.jdk17}/bin/java -XX:+UseParallelGC -Xmx4g \
              -jar ${tla2tools} \
              -config ${./Jolt.cfg} \
              ${./tla/MC_Jolt.tla} \
              -workers auto "$@"
          '';

          # Full verification (TLA+ + Lean tests)
          check-all = pkgs.writeShellScriptBin "jolt-check-all" ''
            echo "=== TLA+ Verification ==="
            ${self.packages.${system}.tla-check}/bin/jolt-tla-check
            echo ""
            echo "=== Lean Tests ==="
            cd ${./lean} && ${pkgs'.lake}/bin/lake exe test
          '';

          default = self.packages.${system}.oracle;
        };

        # === Development Shell ===
        devShells.default = pkgs'.mkShell {
          buildInputs = [
            # Lean toolchain
            pkgs'.lean
            pkgs'.lake

            # TLA+ verification
            pkgs.jdk17

            # Scripts
            pkgs.python311
            pkgs.bash
            pkgs.git
          ];

          TLAPLUS_JAR = "${tla2tools}";

          shellHook = ''
            echo "jolt-tla development shell"
            echo "  Lean:  $(lean --version 2>/dev/null || echo 'v4.26.0')"
            echo "  Java:  $(java --version 2>&1 | head -1)"
            echo "  TLA+:  v1.8.0 (at \$TLAPLUS_JAR)"
            echo ""
            echo "Commands:"
            echo "  lake build         - Build oracle"
            echo "  lake exe oracle    - Run oracle CLI"
            echo "  lake exe test      - Run Lean tests"
            echo "  java -jar \$TLAPLUS_JAR -config Jolt.cfg tla/MC_Jolt.tla"
          '';
        };

        # === Checks (for `nix flake check`) ===
        checks = {
          oracle-build = self.packages.${system}.oracle;
          tla-parse = pkgs.runCommand "tla-parse" {} ''
            ${pkgs.jdk17}/bin/java -cp ${tla2tools} tla2sany.SANY ${./tla/MC_Jolt.tla}
            touch $out
          '';
        };
      }
    ) // {
      # === NixOS Module ===
      nixosModules.default = { config, lib, pkgs, ... }:
        with lib;
        let
          cfg = config.services.jolt-oracle;
        in {
          options.services.jolt-oracle = {
            enable = mkEnableOption "Jolt Oracle executable spec";

            package = mkOption {
              type = types.package;
              default = self.packages.${pkgs.system}.oracle;
              description = "The jolt-oracle package to use";
            };
          };

          config = mkIf cfg.enable {
            environment.systemPackages = [ cfg.package ];
          };
        };

      # === Overlay ===
      overlays.default = final: prev: {
        jolt-oracle = self.packages.${prev.system}.oracle;
        jolt-tla-check = self.packages.${prev.system}.tla-check;
      };
    };
}
