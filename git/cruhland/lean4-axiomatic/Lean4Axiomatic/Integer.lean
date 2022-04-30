import Lean4Axiomatic.Integer.Core

/-!
# Combined typeclass of all integer definitions and properties
-/

namespace Lean4Axiomatic

open Integer (Core)

/--
The class of [integers](https://en.wikipedia.org/wiki/Integer).

The fields of this class express many integer properties. Any type `α` for
which an instance of `Integer α` exists must obey all of them. However, most of
the properties can be derived from a few essential ones, reducing the work
required to construct an instance.

**Named parameters**
- `ℤ`: a type that obeys all of the properties provided by this class.
-/
class Integer (ℤ : Type) where
  toCore : Core ℤ

namespace Integer

attribute [instance] toCore

end Lean4Axiomatic.Integer
