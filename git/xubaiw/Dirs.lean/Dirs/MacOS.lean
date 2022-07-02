import Dirs.Utils

open System

namespace Dirs.MacOS

def home : BaseIO $ Option FilePath :=
  getDirFromEnv? "HOME"

def audio : BaseIO $ Option FilePath :=
  getDirFromEnv? "HOME" ["Library", "Music"]

def cache : BaseIO $ Option FilePath := 
  getDirFromEnv? "HOME" ["Library", "Caches"]

def config : BaseIO $ Option FilePath :=
  getDirFromEnv? "HOME" ["Library", "Application Support"]

def data : BaseIO $ Option FilePath := 
  getDirFromEnv? "HOME" ["Library", "Application Support"]

def dataLocal : BaseIO $ Option FilePath :=
  getDirFromEnv? "HOME" ["Library", "Application Support"]

def desktop : BaseIO $ Option FilePath :=
  getDirFromEnv? "HOME" ["Library", "Desktop"]

def document : BaseIO $ Option FilePath :=
  getDirFromEnv? "HOME" ["Library", "Documents"]

def download : BaseIO $ Option FilePath :=
  getDirFromEnv? "HOME" ["Library", "Downloads"]

def executable : BaseIO $ Option FilePath :=
  return none

def font : BaseIO $ Option FilePath :=
  getDirFromEnv? "HOME" ["Library", "Fonts"]

def picture : BaseIO $ Option FilePath :=
  getDirFromEnv? "HOME" ["Library", "Pictures"]

def preference : BaseIO $ Option FilePath :=
  getDirFromEnv? "HOME" ["Library", "Preferences"]

def public : BaseIO $ Option FilePath := 
  getDirFromEnv? "HOME" ["Library", "Public"]

def runtime : BaseIO $ Option FilePath :=
  return none

def state : BaseIO $ Option FilePath := do
  return none

def template : BaseIO $ Option FilePath :=
  return none

def video: BaseIO $ Option FilePath :=
  getDirFromEnv? "HOME" ["Library", "Movies"]

end Dirs.MacOS
