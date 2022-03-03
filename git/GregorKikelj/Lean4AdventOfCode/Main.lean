import Solution01
import Solution02

def main : IO Unit := do
  let s1 <- solvePart21 "Solved/Day02/input.txt"
  IO.println s1
  let s2 <- solvePart22 "Solved/Day02/input.txt"
  IO.println s2

#eval main