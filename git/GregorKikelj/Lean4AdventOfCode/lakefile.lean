import Lake
open System Lake DSL

package grekiki where 
  dependencies := #[
    { name := `solver, src := Source.path (FilePath.mk "Solved") }
  ]
