/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Util.Git
import Lake.Config.Package
import Lake.Config.Workspace
import Lake.Load.Config

namespace Lake
open Git System

/-- `elan` toolchain file name -/
def toolchainFileName : FilePath :=
  "lean-toolchain"

def gitignoreContents :=
s!"/{defaultBuildDir}
/{defaultPackagesDir}/*
!/{defaultPackagesDir}/{manifestFileName}
"

def libFileContents :=
  s!"def hello := \"world\""

def mainFileName : FilePath :=
  s!"{defaultBinRoot}.lean"

def mainFileContents (libRoot : Name) :=
s!"import {libRoot}

def main : IO Unit :=
  IO.println s!\"Hello, \{hello}!\"
"

def exeFileContents :=
s!"def main : IO Unit :=
  IO.println s!\"Hello, world!\"
"

def stdConfigFileContents (pkgName : Name) (root : Name) :=
s!"import Lake
open Lake DSL

package {pkgName} \{
  -- add package configuration options here
}

lean_lib {root} \{
  -- add library configuration options here
}

@[defaultTarget]
lean_exe {pkgName} \{
  root := `Main
}
"

def exeConfigFileContents (pkgName : Name) (exeRoot : Name) :=
s!"import Lake
open Lake DSL

package {pkgName} \{
  -- add package configuration options here
}

@[defaultTarget]
lean_exe {exeRoot} \{
  -- add executable configuration options here
}
"

def libConfigFileContents (pkgName : Name) (libRoot : Name) :=
s!"import Lake
open Lake DSL

package {pkgName} \{
  -- add package configuration options here
}

@[defaultTarget]
lean_lib {libRoot} \{
  -- add library configuration options here
}
"

def mathConfigFileContents (pkgName : Name) (libRoot : Name) :=
s!"import Lake
open Lake DSL

package {pkgName} \{
  -- add any package configuration options here
}

require mathlib from git
  \"https://github.com/leanprover-community/mathlib4.git\"

@[defaultTarget]
lean_lib {libRoot} \{
  -- add any library configuration options here
}
"

/-- The options for the template argument to `initPkg`. -/
inductive InitTemplate
| std | exe | lib | math
deriving Repr, DecidableEq

def InitTemplate.parse? : String → Option InitTemplate
| "std" => some .std
| "exe" => some .exe
| "lib" => some .lib
| "math" => some .math
| _ => none

def InitTemplate.configFileContents (pkgName root : Name) : InitTemplate → String
| .std => stdConfigFileContents pkgName root
| .lib => libConfigFileContents pkgName root
| .exe => exeConfigFileContents pkgName root
| .math => mathConfigFileContents pkgName root

instance : Inhabited InitTemplate := ⟨.std⟩

/-- Initialize a new Lake package in the given directory with the given name. -/
def initPkg (dir : FilePath) (name : String) (tmp : InitTemplate) : LogIO PUnit := do
  let pkgName := name.decapitalize.toName

  -- determine the name to use for the root
  -- use upper camel case unless the specific module name already exists
  let (root, rootFile, rootExists) ← do
    let root := name.toName
    let rootFile := Lean.modToFilePath dir root "lean"
    let rootExists ← rootFile.pathExists
    if tmp = .exe || rootExists then
      pure (root, rootFile, rootExists)
    else
      let root := toUpperCamelCase root
      let rootFile := Lean.modToFilePath dir root "lean"
      pure (root, rootFile, ← rootFile.pathExists)

  -- write default configuration file
  let configFile := dir / defaultConfigFile
  if (← configFile.pathExists) then
    error  "package already initialized"
  IO.FS.writeFile configFile <| tmp.configFileContents pkgName root

  -- write example code if the files do not already exist
  if tmp = .exe then
    unless (← rootFile.pathExists) do
      IO.FS.writeFile rootFile exeFileContents
  else
    if !rootExists then
      IO.FS.createDirAll rootFile.parent.get!
      IO.FS.writeFile rootFile libFileContents
    if tmp = .std then
      let mainFile := dir / mainFileName
      unless (← mainFile.pathExists) do
        IO.FS.writeFile mainFile <| mainFileContents root

  -- write Lean's toolchain to file (if it has one) for `elan`
  if Lean.toolchain ≠ "" then
    IO.FS.writeFile (dir / toolchainFileName) <| Lean.toolchain ++ "\n"

  -- update `.gitignore` with additional entries for Lake
  let h ← IO.FS.Handle.mk (dir / ".gitignore") IO.FS.Mode.append (bin := false)
  h.putStr gitignoreContents

  -- initialize a `.git` repository if none already
  unless (← FilePath.isDir <| dir / ".git") do
    let repo := GitRepo.mk dir
    try
      repo.quietInit
      unless upstreamBranch = "master" do
        repo.checkoutBranch upstreamBranch
    catch _ =>
      logWarning "failed to initialize git repository"

def init (pkgName : String) (tmp : InitTemplate) : LogIO PUnit :=
  initPkg "." pkgName tmp

def new (pkgName : String) (tmp : InitTemplate) : LogIO PUnit := do
  let dirName := pkgName.map fun chr => if chr == '.' then '-' else chr
  IO.FS.createDir dirName
  initPkg dirName pkgName tmp
