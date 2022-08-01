import Lake
open Lake DSL

package «ring-mwe» {}

@[defaultTarget]
lean_lib ringMwe

require mathlib
  from git "https://github.com/leanprover-community/mathlib4.git"@"8f609e0ed826dde127c8bc322cb6f91c5369d37a"
