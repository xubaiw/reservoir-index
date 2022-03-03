import LeanPlay.Cli

-- #eval Leanpkg.leanVersionString

def main (args : List String) : IO UInt32 := do
  try
    LeanPlay.cli args
    pure 0
  catch e =>
    IO.eprintln <| "error: " ++ toString e -- avoid "uncaught exception: ..."
    pure 1
