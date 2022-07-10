import Lake
open Lake DSL

package clashctl

require socket from
  git "https://github.com/xubaiw/Socket.lean"@"main"

require Cli from
  git "https://github.com/mhuisi/lean4-cli"@"nightly"

lean_lib Clashctl

@[defaultTarget]
lean_exe clashctl {
  root := `Main
}
