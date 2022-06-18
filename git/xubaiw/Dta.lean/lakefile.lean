import Lake
open Lake DSL

package dta

require parsec from
  git "https://github.com/xubaiw/Parsec.lean"@"b6e8721c36bde18bca6a81e7b40d966b401cb329"

lean_lib Dta

@[defaultTarget]
lean_exe dta {
  root := `Main
}
