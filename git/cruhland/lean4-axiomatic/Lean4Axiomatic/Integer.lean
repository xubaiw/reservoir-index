import Lean4Axiomatic.Integer.Addition
import Lean4Axiomatic.Integer.Core
import Lean4Axiomatic.Integer.Multiplication
import Lean4Axiomatic.Integer.Negation

/-!
# Combined typeclass of all integer definitions and properties
-/

namespace Lean4Axiomatic

open Integer (
  Addition.Base Conversion Equality Multiplication.Base Negation.Base
)

/--
The class of [integers](https://en.wikipedia.org/wiki/Integer).

It is parameterized not only on a type `ℤ` that must satisfy the properties of
integers, but also on a type `ℕ` that obeys the properties of natural numbers
(via `Natural ℕ`). This is to support the crucial fact that a bijection exists
between the natural numbers and the nonnegative integers (provided by
`Integer.Conversion.from_natural`).

Although there are many integer properties expressed by this class, most of
them can be derived from a few essential ones, reducing the work required to
construct an instance.

**Named parameters**
- `ℕ`: A type that obeys all of the properties of the natural numbers.
- `ℤ`: A type that obeys all of the properties provided by this class.

**Class parameters**
- `Natural ℕ`: Evidence that `ℕ` implements the natural numbers.
-/
class Integer (ℕ : Type) [Natural ℕ] (ℤ : Type) :=
  toEquality : Equality ℤ
  toConversion : Conversion ℕ ℤ
  toAddition : Addition.Base ℕ ℤ
  toNegation : Negation.Base ℕ ℤ
  toMultiplication : Multiplication.Base ℕ ℤ

namespace Integer

attribute [instance] toConversion
attribute [instance] toEquality

export Addition (addOp)
export Equality (eqvOp)
export Multiplication (mulOp)
export Negation (negOp)

end Lean4Axiomatic.Integer
