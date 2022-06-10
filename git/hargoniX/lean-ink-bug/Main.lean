import LeanInk
import Demo

def main : IO Unit := do
  let inputPath := System.FilePath.mk "Mathlib/Data/Option/Defs.lean"
  let config := {
    inputFilePath := inputPath
    inputFileContents := (← IO.FS.readFile inputPath)
    lakeFile := none
    verbose := true
    experimentalTypeInfo := true
    experimentalDocString := true
    experimentalSemanticType := true
    prettifyOutput := true
    : LeanInk.Configuration
  }
  let result ← LeanInk.Analysis.analyzeInput config
  IO.println s!"Hello, {hello}!"
