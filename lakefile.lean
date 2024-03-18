import Lake
open Lake DSL

require std from git "https://github.com/leanprover/std4" @ "main"

package «impdf» where
  -- add package configuration options here

lean_lib «Impdf» where
  -- add library configuration options here

@[default_target]
lean_exe «impdf» where
  root := `Main
