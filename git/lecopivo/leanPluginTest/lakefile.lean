import Lake
open Lake DSL

package Package {
  defaultFacet := PackageFacet.sharedLib
  moreLinkArgs := #["-L~/.elan/toolchains/leanprover--lean4---nightly/lib/lean", "-lleanshared"]
  dependencies := #[{
    name := `mathlib
    src := Source.git "https://github.com/leanprover-community/mathlib4.git" "c4c15e058c5e1e1c5316257abdcb2fc2a7fa54c4"
  }]
}
