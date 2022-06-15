import Lake
open Lake DSL

package LeanUtils

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"4f6c829ae8455e8d3f01322dd4cfe753e68393ed"

@[defaultTarget]
lean_exe LeanUtils where
  root := `Main
  supportInterpreter := true