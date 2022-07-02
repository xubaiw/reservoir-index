open System

namespace Dirs

def getDirFromEnv? (s : String) (exts : List FilePath := []) : BaseIO $ Option FilePath := do
  if let some d ← IO.getEnv s then
    let d := exts.foldl (λ acc x => acc.join x) (FilePath.mk d)
    return if ←d.isDir then some d else none
  else return none

end Dirs
