import Lake
open System Lake DSL

package bar2 (pkgDir) (args) do
  let current ← IO.currentDir
  let dylibDir := current / ".." / "bar1" / "build" / "lib" 
  let dylib := dylibDir / s!"libbar1.{sharedLibExt}"
  IO.println s!"link to {dylib}"
  return {
    name := `bar2
    moreLibTargets := #[
      inputFileTarget dylib
    ]
    moreLinkArgs := #["-l", "bar1", "-L", dylibDir.toString]
  }
