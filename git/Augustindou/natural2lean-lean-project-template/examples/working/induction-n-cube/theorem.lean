import LeanUtils
open Nat

theorem n_cube_plus_2_n (n : Nat) : divisible 3 (n^3 + 2*n) := by
  match n with
  | 0 => repeat (first | trivial | ring | simp_all)
  | k+1 => 
    have h₁ : divisible 3 (k ^ 3 + 2 * k) := n_cube_plus_2_n _

    have ⟨z, h₂⟩ : ∃ z, k^3 + 2*k = 3*z := by
      repeat (first | ring | simp_all)
    
    have h₃ : (k + 1) ^ 3 + 2 * (k + 1) = 3*(z + k^2 + k + 1) := by
      calc
        (k + 1) ^ 3 + 2 * (k + 1) = k^3 + 3*k^2 + 5*k + 3 := by 
          repeat (first | ring | simp_all)
        _ = k^3 + 2*k + 3 * (k^2 + k + 1) := by 
          repeat (first | ring | simp_all)
        _ = 3*z + 3 * (k^2 + k + 1) := by
          repeat (first | ring | simp_all)
        _ = 3 * (z + k^2 + k + 1) := by
          repeat (first | ring | simp_all)
    try rw [h₃]
  
    apply mod_rewrite.mpr
    exact ⟨_, by repeat (first | trivial | ring | simp_all)⟩



