import LeanUtils
open Nat

theorem square_mod_3 (q : Nat) : (¬divisible 3 q) → (q^2 % 3 = 1) := by
  intros h₁
  apply mod_rewrite.mpr
  have h2 : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by (first | exact mod_2_poss _ | exact mod_3_poss _ | exact mod_4_poss _ | exact mod_5_poss _)

  -- divide cases into 3 goals
  rcases h2 with h2 | h2 | h2

  contradiction

  have ⟨k, h3⟩ : ∃ (k : Nat), q = 3 * k + 1 := by 
    simp_all

  have q_square : q^2 = 3 * (3 * k^2 + 2 * k) + 1  := by 
    calc
      q^2 = (3 * k + 1)^2 := by 
        repeat (first | ring | simp_all)
      _ = 9 * k^2 + 6 * k + 1 := by 
        repeat (first | ring | simp_all)
      _ = 3 * (3 * k^2 + 2 * k) + 1 := by 
        repeat (first | ring | simp_all)
  
  exact ⟨_, by assumption⟩

  have ⟨k, h3⟩ : ∃ (k : Nat), q = 3 * k + 2 := by 
    simp_all
  have q_square : q^2 = 3 * (3 * k^2 + 4 * k + 1) + 1 := by 
    calc
      q^2 = (3 * k + 2)^2 := by 
        repeat (first | ring | simp_all)
      _ = 3 * (3 * k^2 + 4 * k + 1) + 1 := by 
        repeat (first | ring | simp_all)
  
  exact ⟨_, by assumption⟩