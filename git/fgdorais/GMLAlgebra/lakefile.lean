import Lake
open Lake DSL

package GMLAlgebra {
  defaultFacet := PackageFacet.oleans
  dependencies := #[{
    name := `GMLInit
    src := Source.git "https://github.com/fgdorais/GMLInit.git" "384f93fb25b8d6e81dcf2abc396d9472568d88af"
  }]
}
