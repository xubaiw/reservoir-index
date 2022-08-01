import Lake
open Lake DSL

package ffi {
  -- add package configuration options here
}

lean_lib FFI {
  
}

-- how to arbitrary string as identifier?
@[defaultTarget]
lean_exe ffi_test {
  root := `Main
}
