import Lake
open Lake DSL

package «test-mathlib» {
    dependencies := #[{
      name := `mathlib
      src := Source.git "https://github.com/hargonix/mathlib4" "4f37dca85ad9d0e8e18c080a9d22cec86593d6b5"
    }]
}
