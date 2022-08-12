import Lake
open Lake DSL

package graphs_groups {
  -- add package configuration options here
}

lean_lib GraphsGroups {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe graphs_groups {
  root := `Main
}

require mathlib from git 
"https://github.com/leanprover-community/mathlib4.git"