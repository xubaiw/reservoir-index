import Lake
open Lake DSL

package untyped {
  -- add configuration options here
  dependencies := #[
    {
      name := `mathlib
      src := Source.git "https://github.com/leanprover-community/mathlib4" "6895646674b04c0d7bcd085b4da3f7bb354ceaa9"
    }
  ]
}
