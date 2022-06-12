import Lean4Axiomatic.Integer.Addition
import Lean4Axiomatic.Integer.Core
import Lean4Axiomatic.Integer.Multiplication

/-!
# Combined typeclass of all integer definitions and properties
-/

namespace Lean4Axiomatic

open Integer (Addition.Base Core Equality Multiplication.Base)

/--
The class of [integers](https://en.wikipedia.org/wiki/Integer).

The fields of this class express many integer properties. Any type `α` for
which an instance of `Integer α` exists must obey all of them. However, most of
the properties can be derived from a few essential ones, reducing the work
required to construct an instance.

**Named parameters**
- `ℤ`: a type that obeys all of the properties provided by this class.
-/
class Integer (ℤ : Type) :=
  toCore : Core ℤ
  toAddition : Addition.Base ℤ
  toMultiplication : Multiplication.Base ℤ

namespace Integer

attribute [instance] toCore

export Addition (addOp)
export Equality (eqvOp)
export Multiplication (mulOp)

end Lean4Axiomatic.Integer
