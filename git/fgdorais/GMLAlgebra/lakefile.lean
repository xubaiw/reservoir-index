import Lake
open Lake DSL

package GMLAlgebra {
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
}

@[defaultTarget]
lean_lib GMLAlgebra {}

require GMLInit from git "https://github.com/fgdorais/GMLInit.git"@"4e5230249bd8788a7880d11d05436ee4b70b6c33"
