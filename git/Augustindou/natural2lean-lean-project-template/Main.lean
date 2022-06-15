import LeanUtils
def main : IO Unit := IO.println s!"Hello, world!"
open Nat

example (m : Nat) (h₀ : odd (m)) : even (m^3 + 1) := by

  have ⟨n, h₁⟩ : ∃ (n : Nat), m = 2*n + 1 := by simp at *; assumption

  have h₂ : m^3 + 1 = 2 *(4*n^3 + 6*n^2 + 3*n + 1) := by 
    calc
      m^3 + 1 = (2*n + 1)^3 + 1 := by try simp_all; try ring
      _ = 8*n ^ 3 + 12 *n ^ 2 + 6 *n + 2 := by try simp_all; try ring
      _ = 2 *(4*n^3 + 6*n^2 + 3*n + 1) := by try simp_all; try ring

  exact ⟨_, by assumption⟩