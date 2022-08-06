import Lake
open Lake DSL

package targets {
  srcDir := "src"
}

@[defaultTarget]
lean_lib foo
lean_lib bar
lean_lib baz

lean_exe a
lean_exe b

@[defaultTarget]
lean_exe c

@[defaultTarget]
target meow (pkg : Package) : Unit := do
  IO.FS.writeFile (pkg.buildDir / "meow.txt") "Meow!"
  return .nil

target bark : Unit := do
  logInfo "Bark!"
  return .nil

package_facet print_name pkg : Unit := do
  IO.println pkg.name
  return .nil

module_facet get_src mod : FilePath := do
  inputFile mod.leanFile

module_facet print_src mod : Unit := do
  (← fetch (mod.facet `get_src)).bindSync fun src trace => do
    IO.println src
    return ((), trace)

library_facet print_name lib : Unit := do
  IO.println lib.name
  return .nil
