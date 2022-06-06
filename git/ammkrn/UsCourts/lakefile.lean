import Lake
open Lake DSL

package UsCourts {
  dependencies := #[
    {
      name := `Timelib
      src := Source.git "https://github.com/ammkrn/timelib.git" "main"
    }
  ]
  defaultFacet := PackageFacet.staticLib
}
