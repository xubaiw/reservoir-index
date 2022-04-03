import Lean
import FunnyLang

open Lean

def main : List String → IO Unit
  | [f] => do
    let code ← IO.FS.readFile ⟨f⟩
    initSearchPath (← Lean.findSysroot) ["build/lib"]
    let env ← importModules [{ module := `FunnyLang.Parser }] {}
    match ← parse code env with
    | (none    , p) =>
      let (c, r) := p.run default
      IO.println r
      IO.println c
    | (some msg, _) => IO.eprintln msg
  | _   => do
    let appName := (← IO.appPath).fileName.getD "extern"
    IO.eprintln s!"Usage: {appName} <fny-file>"
