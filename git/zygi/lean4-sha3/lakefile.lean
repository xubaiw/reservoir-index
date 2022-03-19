import Lake
open Lake DSL System

def ffiOTarget (pkgDir : FilePath) : FileTarget :=
  let oFile := pkgDir / defaultBuildDir / "native.o"
  let srcTarget := inputFileTarget <| pkgDir / "native.c"
  fileTargetWithDep oFile srcTarget fun srcFile => do
    compileO oFile srcFile #["-std=c11", "-O3", "-I", (← getLeanIncludeDir).toString, "-I", "tiny_sha3"] "cc"

def keccakOTarget (pkgDir : FilePath) : FileTarget :=
  let oFile := pkgDir / defaultBuildDir / "sha3.o"
  let srcTarget := inputFileTarget <| pkgDir / "tiny_sha3/sha3.c"
  fileTargetWithDep oFile srcTarget fun srcFile => do
    compileO oFile srcFile #["-std=c11", "-O3"] "cc"

def cLibTarget (pkgDir : FilePath) : FileTarget :=
  let libFile := pkgDir / defaultBuildDir / "liblean_sha3_native.a"
  staticLibTarget libFile #[ffiOTarget pkgDir, keccakOTarget pkgDir]

def cSharedLibTarget (pkgDir : FilePath) : FileTarget :=
  let libFile := pkgDir / defaultBuildDir / "lean_sha3_native.so"
  leanSharedLibTarget libFile #[
    ffiOTarget pkgDir,
    keccakOTarget pkgDir,
    -- TODO : hack for now - make this nicer
    inputFileTarget "./build/ir/Sha3.o"]

package sha3 (pkgDir) {
  moreLibTargets := #[cSharedLibTarget pkgDir, cLibTarget pkgDir],
  supportInterpreter := true
}
