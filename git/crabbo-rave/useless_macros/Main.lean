import Macros

def main : IO Unit :=
   let hello := "world!" in IO.println s!"Hello, {hello}!";
