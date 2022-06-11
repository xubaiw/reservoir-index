import Lake
open Lake DSL

package demo {
  supportInterpreter := true
  dependencies := #[
    {
      name := `leanInk
      src := Source.git "https://github.com/leanprover/LeanInk" "10bb456fa4677e791bdd4e195e2205476a55f7dd"
    }
  ]
}
