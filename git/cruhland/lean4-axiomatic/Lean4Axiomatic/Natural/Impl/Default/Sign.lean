import Lean4Axiomatic.Natural.Sign

namespace Lean4Axiomatic
namespace Natural

namespace Default

variable {ℕ : Type}
variable [Core ℕ]

instance sign_base : Sign.Base ℕ := {
  Positive := λ n => n ≄ 0
  positive_neqv_zero := id
  positive_defn := Iff.intro id id
}

end Default

end Natural
end Lean4Axiomatic
