import Lake
open Lake DSL

package GMLAlgebra {
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
}

@[defaultTarget]
lean_lib GMLAlgebra {}

require GMLInit from git "https://github.com/fgdorais/GMLInit.git"@"3015c29225907896289972f964bcc567352e9a60"
