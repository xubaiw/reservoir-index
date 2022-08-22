import Monads


def liftIO (t : ExceptT String Id α) : IO α := do
  match t with
  | .ok r => EStateM.Result.ok r
  | .error s => EStateM.Result.error s

instance : MonadLift (ExceptT String Id) IO where
  monadLift := liftIO

-- set_option trace.Meta.synthInstance true in
def main (args: List String): IO Unit := do
  try
    let ret ← divideRefactored 5 0 |>.run args |>.run 10
    IO.println (toString ret)
  catch e =>
    IO.println e

#eval main []           -- can't divide by zero
#eval main ["--limit"]  -- too many divides
