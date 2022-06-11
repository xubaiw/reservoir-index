import Lake
open Lake DSL

package LeanUtils {
  dependencies := #[{
    name := "mathlib",
    src := Source.git "https://github.com/leanprover-community/mathlib4.git" "fa4c522b1f642cd781aff6d19b80884cfb844ff0"
  }]
}
