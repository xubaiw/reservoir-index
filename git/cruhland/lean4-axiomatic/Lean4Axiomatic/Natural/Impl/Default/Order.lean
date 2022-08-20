import Lean4Axiomatic.Natural.Order

namespace Lean4Axiomatic.Natural.Default

variable {ℕ : Type}
variable [Core ℕ]
variable [Addition ℕ]

local instance : LE ℕ := LE.mk λ n m => ∃ k : ℕ, n + k ≃ m
local instance : LT ℕ := LT.mk λ n m => n ≤ m ∧ n ≄ m

instance order : Order ℕ := {
  leOp := inferInstance
  le_defn := Iff.intro id id

  ltOp := inferInstance
  lt_defn := Iff.intro id id
}

end Lean4Axiomatic.Natural.Default
