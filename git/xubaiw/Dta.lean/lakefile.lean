import Lake
open Lake DSL

package dta

require parsec from
  git "https://github.com/xubaiw/Parsec.lean"@"main"

lean_lib Dta

@[defaultTarget]
lean_exe dta {
  root := `Main
}
