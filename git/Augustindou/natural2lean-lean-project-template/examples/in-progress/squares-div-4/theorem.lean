import LeanUtils
open Nat

theorem squares_div_4 (a b c : Nat) (h₀ : divisible 4 (a^2 + b^2 + c^2)) : divisible 4 (a^2) ∧ divisible 4 (b^2) ∧ divisible 4 (c^2) := by

  admit