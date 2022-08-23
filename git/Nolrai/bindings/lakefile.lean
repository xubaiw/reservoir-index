import Lake
open Lake DSL

package bindings {
  -- add package configuration options here
}

lean_lib Bindings {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe bindings {
  root := `Main
}
