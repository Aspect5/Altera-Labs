import Lake
open Lake DSL

package «lean_verifier» where
  -- add package configuration options here

lean_lib «LeanVerifier» where
  -- add library configuration options here

@[default_target]
lean_exe «lean_verifier» where
  root := `Main
