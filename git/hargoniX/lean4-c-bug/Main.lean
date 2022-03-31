import TestMathlib
import Mathlib.Testing.SlimCheck.Testable

open SlimCheck

def main : IO Unit := do
  -- works Testable.check (∀ (x y z a : Nat) (h1 : 3 < x) (h2 : 3 < y), x - y = y - x) { Configuration.verbose with randomSeed := some 10000}
  -- fails
  Testable.check (∀ (x y z a : Nat) (h1 : 3 < x) (h2 : 3 < y), x - y = y - x) { Configuration.verbose with randomSeed := some 1000}
