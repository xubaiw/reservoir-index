import Lake
open Lake System DSL

package curl {
  moreLeancArgs := #["-lcurl"]
}

require alloy from
  git "https://github.com/tydeu/lean4-alloy"@"main"

module_data alloy.c.o : ActiveFileTarget

@[defaultTarget]
lean_lib Curl {
  precompileModules := true
  nativeFacets := #[Module.oFacet, &`alloy.c.o]
}
