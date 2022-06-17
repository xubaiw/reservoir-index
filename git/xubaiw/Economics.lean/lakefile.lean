import Lake
open Lake DSL

package economics {
  -- add package configuration options here
}

lean_lib Economics {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe economics {
  root := `Main
}
