namespace Nat

variable {n : Nat}

theorem ge_one_of_gt_zero : n > 0 → n ≥ 1 := by
  induction n <;> simp_arith

end Nat