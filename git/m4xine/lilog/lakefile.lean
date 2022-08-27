import Lake
open Lake DSL

package lilog 

lean_lib Lilog

@[defaultTarget]
lean_exe lilog where 
  root := `Lilog.Main