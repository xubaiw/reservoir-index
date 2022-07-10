import Clashctl
import Cli

open Cli

/-!
## Command Runners
-/

def doNothing (_ : Parsed) : IO UInt32 :=
  return 0

def runDelayCmd (p : Parsed) : IO UInt32 := do
  let timeout := p.flag? "timeout" |>.bind (·.as? Nat) |>.getD 5000
  let url := p.flag? "url" |>.bind (·.as? String) |>.getD "https://google.com"
  let r ← getDelays url timeout
  r.forM λ k v => IO.println s!"{k} => {v}"
  return 0

def runGetCmd (_ : Parsed) : IO UInt32 := do
  let r ← getProxy
  IO.println r
  return 0

def runSetCmd (p : Parsed) : IO UInt32 := do
  if let some n := p.positionalArg? "name" |>.bind (·.as? String) then
    match ←setProxy n with
    | true => 
      IO.println "success!"
      return 0
    | false =>
      IO.eprintln "fail"
      return 2
  else
    IO.eprintln "no name provided"
    return 1

/-!
## Commands
-/

def delayCmd := `[Cli|
  delay VIA runDelayCmd; ["0.0.1"]
  "Get delays"
  
  FLAGS:
    timeout: Nat; "Timeout of delay testing, default to 5000"
    url : String; "The URL to test delay, default to https://google.com"
]

def getCmd := `[Cli|
  get VIA runGetCmd; ["0.0.1"]
  "Return the current proxy"
]

def setCmd := `[Cli|
  set VIA runSetCmd; ["0.0.1"]
  "Set proxy group to use one proxy"
  
  ARGS:
    name : String; "The name of the proxy to set"
]

def clashctlCmd : Cmd := `[Cli|
  clashctl VIA doNothing; ["0.0.1"]
  "This string denotes the description of `exampleCmd`."

  SUBCOMMANDS:
    delayCmd;
    setCmd;
    getCmd
]

/-!
## Run the commands
-/

def main (args : List String) : IO UInt32 := do
  clashctlCmd.validate args