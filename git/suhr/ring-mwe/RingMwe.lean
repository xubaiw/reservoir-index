import Mathlib

def hello := "world"

example {n:Nat}: ∀i, i + (↑n-1-i) = ↑n-1 :=
by
  intro i
  ring
