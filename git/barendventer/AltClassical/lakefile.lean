import Lake
open Lake DSL

package altclassical {
  -- add package configuration options here
}

lean_lib AltClassical {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe altclassical {
  root := `Main
}
