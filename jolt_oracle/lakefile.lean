import Lake
open Lake DSL

package jolt_oracle where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib Jolt where
  roots := #[`Jolt]

lean_exe oracle where
  root := `CLI.Main

lean_exe test where
  root := `Tests.Main
