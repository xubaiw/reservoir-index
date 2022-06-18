import Lake
open Lake DSL

package WaterSortPuzzle {
  binName := "wsp"
  dependencies := #[{
    name := `mathlib
    src := .git "https://github.com/leanprover-community/mathlib4.git" "84ca33e940678954dc146f732f447ddc8984cf39"
  }]
}
