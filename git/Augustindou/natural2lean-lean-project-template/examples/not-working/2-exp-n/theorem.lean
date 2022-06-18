-- proving 2^n > n^2 - 1

-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/.E2.9C.94.20lean4.20induction.20with.20multiple.20base.20cases

import LeanUtils
open Nat


theorem two_exp_n (n : Nat) : 2^n > n^2 - 1 := by
  match n with
  | 0 => simp
  | 1 => simp
  | 2 => simp
  | k+3 =>
    have h₁ : 2^(k+2) > (k+2)^2 - 1 := two_exp_n (k + 2)
    have h₂ : (k+3) >= 3 := by simp_arith
    have h₃ : 2^(k+3) > (k+3)^2 - 1 := by calc
      -- ring should be able to solve these types of equalities when fully implemented
      2^(k+3) = 2 * 2^(k+2) := by admit
      -- linarith should be able to solve this when implemented, but currently only in lean3
      _ > 2 * ((k+2)^2 - 1) := by admit
      _ = (k+2) ^ 2 + (k+2) ^ 2  - 2 := by admit
      _ ≥ (k+2) ^ 2 + 3 * k - 2 := by admit
      _ ≥ (k+2) ^ 2 + 2 * k + 1 := by admit
      -- The following should be >, but gives 
      --    invalid 'calc' step, failed to synthesize `Trans` instance 
      --    Trans GT.gt GT.gt ?m.4046Lean
      _ ≥ (k+2) ^ 2 + 2 * k := by admit
      _ = (k+3) ^ 2 - 1 := by admit

    assumption










    