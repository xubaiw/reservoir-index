import Lean4Axiomatic.Natural.Addition
import Lean4Axiomatic.Sign

/-!
# Natural number signedness: definitions and fundamental properties

There are no negative natural numbers, so this file covers positive numbers and
zero.
-/

namespace Lean4Axiomatic.Natural

open Signed (Positive)

/--
Definition of positive natural numbers.

All other properties of positive natural numbers can be derived from this.
-/
class Sign (ℕ : Type) [Core ℕ] :=
  /-- Definition, properties, and syntax for the `Positive` predicate. -/
  positivity : Signed.Positivity ℕ

attribute [instance] Sign.positivity

end Lean4Axiomatic.Natural
