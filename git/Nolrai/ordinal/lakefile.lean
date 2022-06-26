import Lake
open Lake DSL

package ordinal {
  -- add package configuration options here
}

lean_lib Ordinal {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe ordinal {
  root := `Main
}
