import Lake
open Lake DSL System

package TestPrettyPrinter {
  -- add configuration options here
}

script test do
  let libPath := FilePath.mk "build" / "lib"
  let binPath := FilePath.mk "build" / "bin" / "TestPrettyPrinter"
  let runExamples ← IO.Process.output {
    cmd := binPath.withExtension FilePath.exeExtension |>.toString
    args := #["Foo.lean"]
    env := #[("LEAN_PATH", SearchPath.toString [libPath])]
  }
  if runExamples.exitCode ≠ 0 then
    IO.eprint runExamples.stderr
  if runExamples.stdout ≠ "" then
    IO.print runExamples.stdout
  return runExamples.exitCode
