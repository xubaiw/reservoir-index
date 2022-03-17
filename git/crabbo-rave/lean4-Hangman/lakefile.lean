import Lake
open Lake DSL

package Hangman {
  -- add configuration options here
  dependencies := #[
    { name := `«doc-gen4», src := Source.git "https://github.com/leanprover/doc-gen4.git" "main" }
  ]
}
