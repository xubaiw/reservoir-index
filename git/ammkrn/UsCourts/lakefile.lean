import Lake
open Lake DSL

package UsCourts

@[defaultTarget]
lean_lib UsCourts

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"58f072fdbfd5dd77c98d8393a489ed3eff383ac8"

require Timelib from git
  "https://github.com/ammkrn/timelib.git"@"master"

--require Timelib from ".."/"Timelib"
--require mathlib from ".."/"Mathlib4"

