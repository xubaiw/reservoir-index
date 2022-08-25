import Lake
open Lake DSL

package mathport

-- Please ensure that `lean-toolchain` points to the same release of Lean 4
-- as this commit of mathlib4 uses.
require mathlib from git "https://github.com/leanprover-community/mathlib4"@"master"

lean_lib Mathport

@[defaultTarget]
lean_exe mathport where
  root := `MathportApp
  supportInterpreter := true

@[defaultTarget]
lean_exe printast where
  root := `PrintAST