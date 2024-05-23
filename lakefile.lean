import Lake
open Lake DSL

package «default» where
  -- add package configuration options here

lean_lib «Default» where
  -- add library configuration options here

@[default_target]
lean_exe «default» where
  root := `Main
