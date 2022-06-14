-- proving 2^n > n^2 - 1

import LeanUtils
open Nat


-- theorem two_exp_n : (n : Nat) → 2^n > n^2 - 1
--   | 0 => by simp
--   | 1 => by simp
--   | 2 => by simp
--   | k+3 => by admit
    
-- theorem threeBase
--   {motive : Nat → Prop}
--   (minor0 : motive 0)
--   (minor1 : motive 1)
--   (minor2 : motive 2)
--   (minor3 : ∀ n, n >= 3 → motive n)
--   (m : Nat) : motive m :=
--   match h : m with
--   | 0 => minor0
--   | 1 => minor1
--   | 2 => minor2
--   | x+3 =>
--     have hGe : (x+3) >= 3 := by simp_arith
--     minor3 (x+3) hGe

theorem two_exp_n (n : Nat) : 2^n > n^2 - 1 := by
  match n with
  | 0 => simp
  | 1 => simp
  | 2 => simp
  | k+3 =>
    have h₁ : 2^(k+2) > (k+2)^2 - 1 := two_exp_n (k + 2)
    have h₂ : (k+3) >= 3 := by simp_arith
    have h₃ : 2^(k+3) > (k+3)^2 - 1 := by calc
      2^(k+3) = 2 * 2^(k+2) := by 
        try simp_all; try ring
      _ > 2 * ((k+2)^2 - 1) := by 
        try simp_all; try ring

    --  $2^{k+1} = 2 \cdot 2^k > 2 \cdot (k^2 - 1) = k^2 + k^2 - 2 \geq k^2 + 3k - 2 \geq k^2 + 2k + 1 \gt k^2 + 2k = (k+1)^2 - 1$ 



-- ring does not work, should it work when fully implemented ?
example (n : Nat) : 2^(n+1) = 2 * 2^n := by 
  admit 

-- ring and simp only work with equalities, similar tactic for inequalities ? 
example (m n : Nat) (h₁ : m > n): 2 * m > 2 * n := by
  admit

-- theorem two_exp_n (n : Nat) : 2^n > n^2 - 1 := by
--   induction n using threeBase with
--   | minor0 => simp
--   | minor1 => simp
--   | minor2 => simp
--   | minor3 x => 
--     admit












    