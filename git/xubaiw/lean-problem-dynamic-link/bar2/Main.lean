@[extern "bar1_greet"]
constant greet : String → String

def main : IO Unit :=
  IO.println <| greet "Lean Programmers"