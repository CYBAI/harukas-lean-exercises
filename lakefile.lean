import Lake
open Lake DSL

package «default» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_exe «default» where
  root := `Main
