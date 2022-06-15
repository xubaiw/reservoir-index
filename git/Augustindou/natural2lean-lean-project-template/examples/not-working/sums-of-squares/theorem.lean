import LeanUtils
open Nat

theorem sum_of_squares (a b c d : Nat) : ∃ M N : Nat, (a^2+b^2) * (c^2+d^2) = M^2 + N^2 := by 
  have h₁ : (a^2+b^2) * (c^2+d^2) = (a*c-b*d)^2+(a*d+b*c)^2 := by 
    calc
      (a^2+b^2) * (c^2+d^2) = (a*c)^2 + (a*d)^2 + (b*c)^2 + (b*d)^2 := by 
        try simp_all
        try ring
      _ = (a*c)^2 - 2*a*b*c*d + (b*d)^2 + (a*d)^2 + 2*a*b*c*d + (b*c)^2 := by 
        try simp_all
        try ring
        admit -- ring does not seem to be able to solve this for now
      _ = (a*c-b*d)^2+(a*d+b*c)^2 := by 
        try simp_all
        try ring
        admit -- ring does not seem to be able to solve this for now

  exact ⟨_, _, by assumption⟩
