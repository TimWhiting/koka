import Lake
open Lake DSL

package «dmcfa» where
  version := v!"0.1.0"

lean_lib «DMCFA» where
  -- add library configuration options here

@[default_target]
lean_exe «dmcfa» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
