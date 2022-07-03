import AltClassical
open AltClassical
def hello: String := CPos.valueOf (CPos.lift "world")

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
