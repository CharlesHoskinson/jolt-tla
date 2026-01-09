import Lake
open Lake DSL

package jolt_oracle where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "v4.26.0"

@[default_target]
lean_lib Jolt where
  roots := #[`Jolt]

lean_lib CLI where
  roots := #[`CLI.Terminal.Style, `CLI.Terminal.Doc, `CLI.Terminal.RenderPlain,
             `CLI.Terminal.RenderAnsi, `CLI.Report.Types, `CLI.Schema.StateInput,
             `CLI.Schema.ChainInput, `CLI.Schema.TestVector, `CLI.Commands.Digest,
             `CLI.Commands.Verify, `CLI.Commands.VerifyVectors, `CLI.Commands.Generate,
             `CLI.Commands.Status, `CLI.Commands.Explain, `CLI.Commands.Diff,
             `CLI.Commands.Watch, `CLI.Format.Json,
             `CLI.REPL.Types, `CLI.REPL.UI, `CLI.REPL.Errors, `CLI.REPL.Lexer,
             `CLI.REPL.Parser, `CLI.REPL.Eval, `CLI.REPL.Loop]

lean_lib Tests where
  roots := #[`Tests.Main, `Tests.JSONParserTests, `Tests.CLITerminalTests, `Tests.REPLTests]

lean_exe oracle where
  root := `CLI.Main

lean_exe test where
  root := `Tests.Main
