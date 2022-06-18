import Lake
open Lake DSL

package iva {
  -- add package configuration options here
}

lean_lib Iva {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe iva {
  root := `Main
}
