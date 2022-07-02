import Lean
import Dirs.Linux
import Dirs.MacOS

open System Lean

-- TODO: non unix system

namespace Dirs

macro "platform_def" n:ident : command =>
  let n' := n.getId
  `(
    def $n : BaseIO $ Option FilePath :=
      if System.Platform.isOSX then
        $(mkIdent (Name.append `Dirs.MacOS n'))
      else
        $(mkIdent (Name.append `Dirs.Linux n'))
  )

platform_def home
platform_def audio
platform_def cache
platform_def config
platform_def data
platform_def dataLocal
platform_def desktop
platform_def document
platform_def download
platform_def executable
platform_def font
platform_def picture
platform_def preference
platform_def public
platform_def runtime
platform_def state
platform_def template
platform_def video

end Dirs
