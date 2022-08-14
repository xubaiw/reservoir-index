import Lean4Axiomatic.Natural.Sign.Defined

namespace Lean4Axiomatic.Natural.Default

variable {ℕ : Type}
variable [Core ℕ]

open Signed (Positive)

local instance positive_ops : Signed.Positivity.Ops ℕ := {
  Positive := λ n => n ≄ 0
}

def positivity : Signed.Positivity ℕ := {
  positive_defn := Iff.intro id id
}

instance sign : Sign ℕ := {
  positivity := positivity
}

end Lean4Axiomatic.Natural.Default
